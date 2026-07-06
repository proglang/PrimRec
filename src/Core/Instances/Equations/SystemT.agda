{-# OPTIONS --safe #-}

module Core.Instances.Equations.SystemT where

import Data.Fin as Fin
import Data.Nat as Nat
open import Data.Product using (Σ; _,_)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  renaming (subst to substEq)

import System-T as Source
import Core.Contextual.PRHO as Ctx
import Core.Contextual.Equations.PRHO as CtxEq
import Core.Equations.PRHO as PFEq
import Core.Instances.SystemT as SystemT
import Core.PRHO as PF
import Core.Translations.ContextualPRHO as Ctx⇔PF

open Source using (Ty; Ctx; Exp)

infix 4 _≈ₛ_

----------------------------------------------------------------------
-- Capture-avoiding source substitution for the existing intrinsic syntax.
----------------------------------------------------------------------

Ren : ∀ {m n} → Ctx n → Ctx m → Set
Ren Γ Δ = (i : Fin.Fin _) → Σ (Fin.Fin _) (λ j → lookup Δ j ≡ lookup Γ i)

liftRen : ∀ {m n Γ Δ A} → Ren {m} {n} Γ Δ → Ren (A ∷ Γ) (A ∷ Δ)
liftRen ρ Fin.zero = Fin.zero , refl
liftRen ρ (Fin.suc i) with ρ i
... | j , eq = Fin.suc j , eq

rename : ∀ {m n Γ Δ A} → Ren {m} {n} Γ Δ → Exp Γ A → Exp Δ A
rename ρ (Source.Var i) with ρ i
... | j , eq = substEq (Exp _) eq (Source.Var j)
rename ρ (Source.Lam t) = Source.Lam (rename (liftRen ρ) t)
rename ρ Source.CZero = Source.CZero
rename ρ Source.Suc = Source.Suc
rename ρ (Source.App f x) = Source.App (rename ρ f) (rename ρ x)
rename ρ (Source.Nat n) = Source.Nat n
rename ρ (Source.PrecT h z n) =
  Source.PrecT (rename ρ h) (rename ρ z) (rename ρ n)

weakenRen : ∀ {n Γ A} → Ren {Nat.suc n} {n} Γ (A ∷ Γ)
weakenRen i = Fin.suc i , refl

weaken : ∀ {n Γ A B} → Exp {n} Γ A → Exp (B ∷ Γ) A
weaken = rename weakenRen

Sub : ∀ {m n} → Ctx n → Ctx m → Set
Sub Γ Δ = (i : Fin.Fin _) → Exp Δ (lookup Γ i)

liftSub : ∀ {m n Γ Δ A} → Sub {m} {n} Γ Δ → Sub (A ∷ Γ) (A ∷ Δ)
liftSub σ Fin.zero = Source.Var Fin.zero
liftSub σ (Fin.suc i) = weaken (σ i)

subst : ∀ {m n Γ Δ A} → Sub {m} {n} Γ Δ → Exp Γ A → Exp Δ A
subst σ (Source.Var i) = σ i
subst σ (Source.Lam t) = Source.Lam (subst (liftSub σ) t)
subst σ Source.CZero = Source.CZero
subst σ Source.Suc = Source.Suc
subst σ (Source.App f x) = Source.App (subst σ f) (subst σ x)
subst σ (Source.Nat n) = Source.Nat n
subst σ (Source.PrecT h z n) =
  Source.PrecT (subst σ h) (subst σ z) (subst σ n)

singleSub : ∀ {n} {Γ : Ctx n} {A} → Exp Γ A → Sub (A ∷ Γ) Γ
singleSub u Fin.zero = u
singleSub u (Fin.suc i) = Source.Var i

subst0 : ∀ {n} {Γ : Ctx n} {A B} → Exp Γ A → Exp (A ∷ Γ) B → Exp Γ B
subst0 u t = subst (singleSub u) t

----------------------------------------------------------------------
-- Source equations for System T.
----------------------------------------------------------------------

data _≈ₛ_ : ∀ {n} {Γ : Ctx n} {A} → Exp Γ A → Exp Γ A → Set where
  reflₛ : ∀ {n} {Γ : Ctx n} {A} {t : Exp Γ A} → t ≈ₛ t
  symₛ : ∀ {n} {Γ : Ctx n} {A} {t u : Exp Γ A} → t ≈ₛ u → u ≈ₛ t
  transₛ : ∀ {n} {Γ : Ctx n} {A} {t u v : Exp Γ A} →
    t ≈ₛ u → u ≈ₛ v → t ≈ₛ v

  Lam-congₛ : ∀ {n} {Γ : Ctx n} {A B}
    {t u : Exp {Nat.suc n} (A ∷ Γ) B} →
    t ≈ₛ u → Source.Lam t ≈ₛ Source.Lam u
  App-congₛ : ∀ {n} {Γ : Ctx n} {A B}
    {f g : Exp {n} Γ (A Source.⇒ B)}
    {x y : Exp Γ A} →
    f ≈ₛ g → x ≈ₛ y → Source.App f x ≈ₛ Source.App g y
  PrecT-congₛ : ∀ {n} {Γ : Ctx n} {A}
    {h h′ : Exp {n} Γ (A Source.⇒ (Source.TyNat Source.⇒ A))}
    {z z′ : Exp Γ A}
    {k k′ : Exp Γ Source.TyNat} →
    h ≈ₛ h′ → z ≈ₛ z′ → k ≈ₛ k′ →
    Source.PrecT h z k ≈ₛ Source.PrecT h′ z′ k′
  subst-congₛ : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {A}
    {σ τ : Sub {m} {n} Γ Δ}
    {t u : Exp Γ A} →
    t ≈ₛ u →
    ((i : Fin.Fin n) → σ i ≈ₛ τ i) →
    subst σ t ≈ₛ subst τ u

  ⇒-βₛ : ∀ {n} {Γ : Ctx n} {A B}
    (t : Exp {Nat.suc n} (A ∷ Γ) B)
    (u : Exp Γ A) →
    Source.App (Source.Lam t) u ≈ₛ subst0 u t
  ⇒-ηₛ : ∀ {n} {Γ : Ctx n} {A B}
    (f : Exp {n} Γ (A Source.⇒ B)) →
    Source.Lam (Source.App (weaken f) (Source.Var Fin.zero)) ≈ₛ f

  PrecT-zeroₛ : ∀ {n} {Γ : Ctx n} {A}
    (h : Exp {n} Γ (A Source.⇒ (Source.TyNat Source.⇒ A)))
    (z : Exp Γ A) →
    Source.PrecT h z Source.CZero ≈ₛ z
  PrecT-sucₛ : ∀ {n} {Γ : Ctx n} {A}
    (h : Exp {n} Γ (A Source.⇒ (Source.TyNat Source.⇒ A)))
    (z : Exp Γ A)
    (k : Exp Γ Source.TyNat) →
    Source.PrecT h z (Source.App Source.Suc k) ≈ₛ
    Source.App (Source.App h (Source.PrecT h z k)) k
  PrecT-nat-zeroₛ : ∀ {n} {Γ : Ctx n} {A}
    (h : Exp {n} Γ (A Source.⇒ (Source.TyNat Source.⇒ A)))
    (z : Exp Γ A) →
    Source.PrecT h z (Source.Nat 0) ≈ₛ z
  PrecT-nat-sucₛ : ∀ {n} {Γ : Ctx n} {A}
    (h : Exp {n} Γ (A Source.⇒ (Source.TyNat Source.⇒ A)))
    (z : Exp Γ A)
    (k : Nat.ℕ) →
    Source.PrecT h z (Source.Nat (Nat.suc k)) ≈ₛ
    Source.App (Source.App h (Source.PrecT h z (Source.Nat k))) (Source.Nat k)

toPRHO : ∀ {n} {Γ : Ctx n} {A} → Exp Γ A → SystemT.⟦ Γ ⟧ᶜ PF.→ᴾ SystemT.⟦ A ⟧ᵀ
toPRHO = SystemT.toPRHO

appPF : ∀ {Γ A B : PF.TY PF.HO} →
  Γ PF.→ᴾ A PF.`⇒ B → Γ PF.→ᴾ A → Γ PF.→ᴾ B
appPF f x = PF.C PF.apply (PF.`# f x)

zeroPF : ∀ {Γ : PF.TY PF.HO} → Γ PF.→ᴾ SystemT.Natᴴ
zeroPF = PF.C (PF.con {G = SystemT.NatF}) (PF.C PF.ι₁ PF.`⊤)

sucBodyPF : ∀ {Γ : PF.TY PF.HO} →
  Γ PF.`× SystemT.Natᴴ PF.→ᴾ SystemT.Natᴴ
sucBodyPF =
  PF.C (PF.con {G = SystemT.NatF})
    (PF.C PF.ι₂ PF.π₂)

sucPF : ∀ {Γ : PF.TY PF.HO} →
  Γ PF.→ᴾ SystemT.Natᴴ PF.`⇒ SystemT.Natᴴ
sucPF = PF.lam sucBodyPF

numeralPF : ∀ {Γ : PF.TY PF.HO} → Nat.ℕ → Γ PF.→ᴾ SystemT.Natᴴ
numeralPF Nat.zero = zeroPF
numeralPF (Nat.suc n) = appPF sucPF (numeralPF n)

baseStepPF : ∀ {Γ A : PF.TY PF.HO} →
  Γ PF.→ᴾ A → PF.`𝟙 PF.`× Γ PF.→ᴾ A
baseStepPF z = PF.C z PF.π₂

succStepPF : ∀ {Γ A : PF.TY PF.HO} →
  Γ PF.→ᴾ A PF.`⇒ SystemT.Natᴴ PF.`⇒ A →
  (A PF.`× SystemT.Natᴴ) PF.`× Γ PF.→ᴾ A
succStepPF h =
  appPF
    (appPF (PF.C h PF.π₂)
      (PF.C PF.π₁ PF.π₁))
    (PF.C PF.π₂ PF.π₁)

stepPF : ∀ {Γ A : PF.TY PF.HO} →
  Γ PF.→ᴾ A PF.`⇒ SystemT.Natᴴ PF.`⇒ A →
  Γ PF.→ᴾ A →
  (SystemT.NatF PF.[ A PF.`× SystemT.Natᴴ ]) PF.`× Γ PF.→ᴾ A
stepPF h z =
  PF.C
    (PF.`case base succ)
    PF.dist-+-×
  where
  base : PF.`𝟙 PF.`× _ PF.→ᴾ _
  base = baseStepPF z

  succ : (_ PF.`× SystemT.Natᴴ) PF.`× _ PF.→ᴾ _
  succ = succStepPF h

precPF : ∀ {Γ A : PF.TY PF.HO} →
  Γ PF.→ᴾ A PF.`⇒ SystemT.Natᴴ PF.`⇒ A →
  Γ PF.→ᴾ A →
  Γ PF.→ᴾ SystemT.Natᴴ →
  Γ PF.→ᴾ A
precPF h z n =
  PF.C (PF.Pr (stepPF h z)) (PF.`# n PF.id)

renVar : ∀ {m} {Δ : Ctx m} {A} →
  Σ (Fin.Fin m) (λ j → lookup Δ j ≡ A) →
  SystemT.⟦ Δ ⟧ᶜ PF.→ᴾ SystemT.⟦ A ⟧ᵀ
renVar {Δ = Δ} (j , refl) = toPRHO (Source.Var {ctx = Δ} j)

renEnv : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} →
  Ren Γ Δ → SystemT.⟦ Δ ⟧ᶜ PF.→ᴾ SystemT.⟦ Γ ⟧ᶜ
renEnv {Γ = []} ρ = PF.`⊤
renEnv {Γ = A ∷ Γ} {Δ = Δ} ρ =
  PF.`# (renEnv {Γ = Γ} {Δ = Δ} (λ i → ρ (Fin.suc i)))
        (renVar (ρ Fin.zero))

subEnv : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} →
  Sub Γ Δ → SystemT.⟦ Δ ⟧ᶜ PF.→ᴾ SystemT.⟦ Γ ⟧ᶜ
subEnv {Γ = []} σ = PF.`⊤
subEnv {Γ = A ∷ Γ} {Δ = Δ} σ =
  PF.`# (subEnv {Γ = Γ} {Δ = Δ} (λ i → σ (Fin.suc i)))
        (toPRHO (σ Fin.zero))

lookup-renEnv : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m}
  (ρ : Ren Γ Δ) (i : Fin.Fin n) →
  PF.C (toPRHO (Source.Var {ctx = Γ} i))
       (renEnv {Γ = Γ} {Δ = Δ} ρ)
    PFEq.≈
  toPRHO (rename {Γ = Γ} {Δ = Δ} ρ (Source.Var {ctx = Γ} i))
lookup-renEnv {Γ = A ∷ Γ} ρ Fin.zero with ρ Fin.zero
... | j , refl = PFEq.×-β₂
lookup-renEnv {Γ = A ∷ Γ} {Δ = Δ} ρ (Fin.suc i) =
  PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
    (PFEq.≈-trans
      (PFEq.C-cong PFEq.≈-refl PFEq.×-β₁)
      (lookup-renEnv {Γ = Γ} {Δ = Δ} (λ j → ρ (Fin.suc j)) i))

lookup-subEnv : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m}
  (σ : Sub Γ Δ) (i : Fin.Fin n) →
  PF.C (toPRHO (Source.Var {ctx = Γ} i))
       (subEnv {Γ = Γ} {Δ = Δ} σ)
    PFEq.≈ toPRHO (σ i)
lookup-subEnv {Γ = A ∷ Γ} σ Fin.zero = PFEq.×-β₂
lookup-subEnv {Γ = A ∷ Γ} {Δ = Δ} σ (Fin.suc i) =
  PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
    (PFEq.≈-trans
      (PFEq.C-cong PFEq.≈-refl PFEq.×-β₁)
      (lookup-subEnv {Γ = Γ} {Δ = Δ} (λ j → σ (Fin.suc j)) i))

renEnv-tail-lift : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {A}
  (ρ : Ren Γ Δ) →
  renEnv {Γ = Γ} {Δ = A ∷ Δ}
    (λ i → liftRen {Γ = Γ} {Δ = Δ} {A = A} ρ (Fin.suc i))
    PFEq.≈ PF.C (renEnv {Γ = Γ} {Δ = Δ} ρ) PF.π₁
renEnv-tail-lift {Γ = []} ρ =
  PFEq.≈-sym PFEq.𝟙-unique
renEnv-tail-lift {Γ = B ∷ Γ} {Δ = Δ} {A = A} ρ with ρ Fin.zero
... | j , refl =
  PFEq.≈-trans
    (PFEq.`#-cong
      (renEnv-tail-lift {Γ = Γ} {Δ = Δ} {A = A}
        (λ i → ρ (Fin.suc i)))
      PFEq.≈-refl)
    (PFEq.≈-sym PFEq.C-#)

renEnv-lift : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {A}
  (ρ : Ren Γ Δ) →
  renEnv {Γ = A ∷ Γ} {Δ = A ∷ Δ}
    (liftRen {Γ = Γ} {Δ = Δ} {A = A} ρ)
    PFEq.≈ PF.map-× (renEnv {Γ = Γ} {Δ = Δ} ρ) PF.id
renEnv-lift {Γ = Γ} {Δ = Δ} {A = A} ρ =
  PFEq.`#-cong
    (renEnv-tail-lift {Γ = Γ} {Δ = Δ} {A = A} ρ)
    (PFEq.≈-sym PFEq.C-idˡ)

renEnv-weaken : ∀ {n} {Γ : Ctx n} {A} →
  renEnv {Γ = Γ} {Δ = A ∷ Γ} weakenRen PFEq.≈ PF.π₁
renEnv-weaken {Γ = []} =
  PFEq.≈-sym PFEq.𝟙-unique
renEnv-weaken {Γ = B ∷ Γ} {A = A} =
  PFEq.≈-trans
    (PFEq.`#-cong
      (PFEq.≈-trans
        (renEnv-tail-lift {Γ = Γ} {Δ = B ∷ Γ} {A = A} weakenRen)
        (PFEq.C-cong renEnv-weaken PFEq.≈-refl))
      PFEq.≈-refl)
    (PFEq.≈-trans
      (PFEq.≈-sym PFEq.C-#)
      (PFEq.≈-trans
        (PFEq.C-cong PFEq.pair-id PFEq.≈-refl)
        PFEq.C-idˡ))

app-congPF :
  ∀ {Γ A B : PF.TY PF.HO}
  {f f′ : Γ PF.→ᴾ A PF.`⇒ B}
  {x x′ : Γ PF.→ᴾ A} →
  f PFEq.≈ f′ → x PFEq.≈ x′ → appPF f x PFEq.≈ appPF f′ x′
app-congPF f≈ x≈ =
  PFEq.C-cong PFEq.≈-refl (PFEq.`#-cong f≈ x≈)

app-precomp :
  ∀ {Γ Δ A B : PF.TY PF.HO}
  {f : Γ PF.→ᴾ A PF.`⇒ B}
  {x : Γ PF.→ᴾ A}
  {h : Δ PF.→ᴾ Γ} →
  PF.C (appPF f x) h PFEq.≈ appPF (PF.C f h) (PF.C x h)
app-precomp =
  PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
    (PFEq.C-cong PFEq.≈-refl PFEq.C-#)

zero-natural :
  ∀ {Γ Δ : PF.TY PF.HO} {h : Δ PF.→ᴾ Γ} →
  zeroPF {Γ = Δ} PFEq.≈ PF.C (zeroPF {Γ = Γ}) h
zero-natural =
  PFEq.≈-sym
    (PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
      (PFEq.C-cong PFEq.≈-refl
        (PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
          (PFEq.C-cong PFEq.≈-refl PFEq.𝟙-unique))))

suc-body-natural :
  ∀ {Γ Δ : PF.TY PF.HO} {h : Δ PF.→ᴾ Γ} →
  PF.C sucBodyPF (PF.map-× h PF.id)
    PFEq.≈
  sucBodyPF
suc-body-natural =
  PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
    (PFEq.C-cong PFEq.≈-refl
      (PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
        (PFEq.C-cong PFEq.≈-refl
          (PFEq.≈-trans PFEq.×-β₂ PFEq.C-idˡ))))

suc-natural :
  ∀ {Γ Δ : PF.TY PF.HO} {h : Δ PF.→ᴾ Γ} →
  sucPF {Γ = Δ} PFEq.≈ PF.C (sucPF {Γ = Γ}) h
suc-natural =
  PFEq.≈-sym
    (PFEq.≈-trans PFEq.lam-precomp
      (PFEq.lam-cong suc-body-natural))

numeral-natural :
  ∀ {Γ Δ : PF.TY PF.HO} {h : Δ PF.→ᴾ Γ} (n : Nat.ℕ) →
  numeralPF {Γ = Δ} n PFEq.≈ PF.C (numeralPF {Γ = Γ} n) h
numeral-natural Nat.zero = zero-natural
numeral-natural (Nat.suc n) =
  PFEq.≈-trans
    (app-congPF suc-natural (numeral-natural n))
    (PFEq.≈-sym app-precomp)

numeral-toPRHO :
  ∀ {n} {Γ : Ctx n} (k : Nat.ℕ) →
  numeralPF {Γ = SystemT.⟦ Γ ⟧ᶜ} k PFEq.≈ toPRHO (Source.Nat {ctx = Γ} k)
numeral-toPRHO Nat.zero = PFEq.≈-refl
numeral-toPRHO (Nat.suc k) =
  app-congPF PFEq.≈-refl (numeral-toPRHO k)

step-congPF :
  ∀ {Γ A : PF.TY PF.HO}
  {h h′ : Γ PF.→ᴾ A PF.`⇒ SystemT.Natᴴ PF.`⇒ A}
  {z z′ : Γ PF.→ᴾ A} →
  h PFEq.≈ h′ → z PFEq.≈ z′ →
  stepPF h z PFEq.≈ stepPF h′ z′
step-congPF h≈ z≈ =
  PFEq.C-cong
    (PFEq.`case-cong
      (PFEq.C-cong z≈ PFEq.≈-refl)
      (app-congPF
        (app-congPF
          (PFEq.C-cong h≈ PFEq.≈-refl)
          PFEq.≈-refl)
        PFEq.≈-refl))
    PFEq.≈-refl

prec-congPF :
  ∀ {Γ A : PF.TY PF.HO}
  {h h′ : Γ PF.→ᴾ A PF.`⇒ SystemT.Natᴴ PF.`⇒ A}
  {z z′ : Γ PF.→ᴾ A}
  {n n′ : Γ PF.→ᴾ SystemT.Natᴴ} →
  h PFEq.≈ h′ → z PFEq.≈ z′ → n PFEq.≈ n′ →
  precPF h z n PFEq.≈ precPF h′ z′ n′
prec-congPF h≈ z≈ n≈ =
  PFEq.C-cong
    (PFEq.Pr-cong (step-congPF h≈ z≈))
    (PFEq.`#-cong n≈ PFEq.≈-refl)

Pr-precomp-parameter :
  ∀ {Γ Δ A : PF.TY PF.HO}
  {step : (SystemT.NatF PF.[ A PF.`× SystemT.Natᴴ ]) PF.`× Γ PF.→ᴾ A}
  {n : Γ PF.→ᴾ SystemT.Natᴴ}
  {n′ : Δ PF.→ᴾ SystemT.Natᴴ}
  {e : Δ PF.→ᴾ Γ} →
  n′ PFEq.≈ PF.C n e →
  PF.C
    (PF.Pr (PF.C step (PF.map-× PF.id e)))
    (PF.`# n′ PF.id)
    PFEq.≈
  PF.C (PF.C (PF.Pr step) (PF.`# n PF.id)) e
Pr-precomp-parameter {step = step} {n = n} {n′ = n′} {e = e} n≈ =
  PFEq.≈-trans
    (PFEq.C-cong
      (PFEq.Pr-parameterʳ {G = SystemT.NatF} {h = step} {k = e})
      PFEq.≈-refl)
    (PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
      (PFEq.≈-trans
        (PFEq.C-cong PFEq.≈-refl PFEq.map-×-#)
        (PFEq.≈-trans
          (PFEq.C-cong PFEq.≈-refl
            (PFEq.`#-cong PFEq.C-idˡ PFEq.≈-refl))
          (PFEq.≈-trans
            (PFEq.C-cong PFEq.≈-refl
              (PFEq.`#-cong n≈ PFEq.≈-refl))
            (PFEq.≈-trans
              (PFEq.C-cong PFEq.≈-refl
                (PFEq.`#-cong PFEq.≈-refl PFEq.C-idʳ))
              (PFEq.≈-sym rhs-to-common))))))
  where
  rhs-to-common :
    PF.C (PF.C (PF.Pr step) (PF.`# n PF.id)) e
      PFEq.≈
    PF.C (PF.Pr step) (PF.`# (PF.C n e) e)
  rhs-to-common =
    PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
      (PFEq.≈-trans
        (PFEq.C-cong PFEq.≈-refl PFEq.C-#)
        (PFEq.C-cong PFEq.≈-refl
          (PFEq.`#-cong PFEq.≈-refl PFEq.C-idˡ)))

second-proj-natural :
  ∀ {Γ Δ L A : PF.TY PF.HO}
  {z : Γ PF.→ᴾ A}
  {e : Δ PF.→ᴾ Γ} →
  PF.C (PF.C z e) PF.π₂
    PFEq.≈
  PF.C (PF.C z PF.π₂) (PF.map-× (PF.id {T = L}) e)
second-proj-natural =
  PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
    (PFEq.≈-sym
      (PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
        (PFEq.C-cong PFEq.≈-refl PFEq.×-β₂)))

baseStep-natural :
  ∀ {Γ Δ A : PF.TY PF.HO}
  {z : Γ PF.→ᴾ A}
  {e : Δ PF.→ᴾ Γ} →
  baseStepPF (PF.C z e)
    PFEq.≈
  PF.C (baseStepPF z) (PF.map-× PF.id e)
baseStep-natural = second-proj-natural

π₁-map-idˡ :
  ∀ {Γ Δ A : PF.TY PF.HO} {e : Δ PF.→ᴾ Γ} →
  PF.C PF.π₁ (PF.map-× (PF.id {T = A}) e) PFEq.≈ PF.π₁
π₁-map-idˡ =
  PFEq.≈-trans PFEq.×-β₁ PFEq.C-idˡ

leftPair-natural :
  ∀ {Γ Δ A B : PF.TY PF.HO} {e : Δ PF.→ᴾ Γ} →
  PF.C (PF.C PF.π₁ PF.π₁) (PF.map-× (PF.id {T = A PF.`× B}) e)
    PFEq.≈
  PF.C PF.π₁ PF.π₁
leftPair-natural =
  PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
    (PFEq.C-cong PFEq.≈-refl π₁-map-idˡ)

rightPair-natural :
  ∀ {Γ Δ A B : PF.TY PF.HO} {e : Δ PF.→ᴾ Γ} →
  PF.C (PF.C PF.π₂ PF.π₁) (PF.map-× (PF.id {T = A PF.`× B}) e)
    PFEq.≈
  PF.C PF.π₂ PF.π₁
rightPair-natural =
  PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
    (PFEq.C-cong PFEq.≈-refl π₁-map-idˡ)

succStep-natural :
  ∀ {Γ Δ A : PF.TY PF.HO}
  {h : Γ PF.→ᴾ A PF.`⇒ SystemT.Natᴴ PF.`⇒ A}
  {e : Δ PF.→ᴾ Γ} →
  succStepPF (PF.C h e)
    PFEq.≈
  PF.C (succStepPF h) (PF.map-× (PF.id {T = A PF.`× SystemT.Natᴴ}) e)
succStep-natural {A = A} {h = h} {e = e} =
  PFEq.≈-trans
    (app-congPF inner-natural (PFEq.≈-sym rightPair-natural))
    (PFEq.≈-sym app-precomp)
  where
  inner-natural :
    appPF (PF.C (PF.C h e) PF.π₂) (PF.C PF.π₁ PF.π₁)
      PFEq.≈
    PF.C
      (appPF (PF.C h PF.π₂) (PF.C PF.π₁ PF.π₁))
      (PF.map-× (PF.id {T = A PF.`× SystemT.Natᴴ}) e)
  inner-natural =
    PFEq.≈-trans
      (app-congPF second-proj-natural (PFEq.≈-sym leftPair-natural))
      (PFEq.≈-sym app-precomp)

map-×-ι₁-right :
  ∀ {Γ Δ A : PF.TY PF.HO} {e : Δ PF.→ᴾ Γ} →
  PF.map-× (PF.ι₁ {U = PF.`𝟙} {V = A}) e
    PFEq.≈
  PF.C (PF.map-× PF.ι₁ (PF.id {T = Γ}))
    (PF.map-× (PF.id {T = PF.`𝟙}) e)
map-×-ι₁-right =
  PFEq.≈-sym
    (PFEq.≈-trans PFEq.map-×-C
      (PFEq.map-×-cong PFEq.C-idʳ PFEq.C-idˡ))

map-×-ι₂-right :
  ∀ {Γ Δ A B : PF.TY PF.HO} {e : Δ PF.→ᴾ Γ} →
  PF.map-× (PF.ι₂ {U = A}) e
    PFEq.≈
  PF.C (PF.map-× PF.ι₂ (PF.id {T = Γ}))
    (PF.map-× (PF.id {T = B}) e)
map-×-ι₂-right =
  PFEq.≈-sym
    (PFEq.≈-trans PFEq.map-×-C
      (PFEq.map-×-cong PFEq.C-idʳ PFEq.C-idˡ))

dist-map-ι₁-right :
  ∀ {Γ Δ A : PF.TY PF.HO} {e : Δ PF.→ᴾ Γ} →
  PF.C (PF.dist-+-× {U = PF.`𝟙} {V = A} {T = Γ})
    (PF.map-× PF.ι₁ e)
    PFEq.≈
  PF.C PF.ι₁ (PF.map-× (PF.id {T = PF.`𝟙}) e)
dist-map-ι₁-right =
  PFEq.≈-trans
    (PFEq.C-cong PFEq.≈-refl map-×-ι₁-right)
    (PFEq.≈-trans PFEq.C-assoc
      (PFEq.C-cong PFEq.dist-map-ι₁ PFEq.≈-refl))

dist-map-ι₂-right :
  ∀ {Γ Δ A B : PF.TY PF.HO} {e : Δ PF.→ᴾ Γ} →
  PF.C (PF.dist-+-× {U = A} {V = B} {T = Γ})
    (PF.map-× PF.ι₂ e)
    PFEq.≈
  PF.C PF.ι₂ (PF.map-× (PF.id {T = B}) e)
dist-map-ι₂-right =
  PFEq.≈-trans
    (PFEq.C-cong PFEq.≈-refl map-×-ι₂-right)
    (PFEq.≈-trans PFEq.C-assoc
      (PFEq.C-cong PFEq.dist-map-ι₂ PFEq.≈-refl))

step-ι₁ :
  ∀ {Γ A : PF.TY PF.HO}
  {h : Γ PF.→ᴾ A PF.`⇒ SystemT.Natᴴ PF.`⇒ A}
  {z : Γ PF.→ᴾ A} →
  PF.C (stepPF h z) (PF.map-× PF.ι₁ PF.id)
    PFEq.≈
  baseStepPF z
step-ι₁ =
  PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
    (PFEq.≈-trans
      (PFEq.C-cong PFEq.≈-refl PFEq.dist-map-ι₁)
      PFEq.+-β₁)

step-ι₂ :
  ∀ {Γ A : PF.TY PF.HO}
  {h : Γ PF.→ᴾ A PF.`⇒ SystemT.Natᴴ PF.`⇒ A}
  {z : Γ PF.→ᴾ A} →
  PF.C (stepPF h z) (PF.map-× PF.ι₂ PF.id)
    PFEq.≈
  succStepPF h
step-ι₂ =
  PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
    (PFEq.≈-trans
      (PFEq.C-cong PFEq.≈-refl PFEq.dist-map-ι₂)
      PFEq.+-β₂)

map-id-ι₁ :
  ∀ {Γ Δ A : PF.TY PF.HO} {e : Δ PF.→ᴾ Γ} →
  PF.C (PF.map-× (PF.id {T = PF.`𝟙 PF.`+ A}) e)
    (PF.map-× PF.ι₁ PF.id)
    PFEq.≈
  PF.map-× PF.ι₁ e
map-id-ι₁ =
  PFEq.≈-trans PFEq.map-×-C
    (PFEq.map-×-cong PFEq.C-idˡ PFEq.C-idʳ)

map-id-ι₂ :
  ∀ {Γ Δ A B : PF.TY PF.HO} {e : Δ PF.→ᴾ Γ} →
  PF.C (PF.map-× (PF.id {T = A PF.`+ B}) e)
    (PF.map-× PF.ι₂ PF.id)
    PFEq.≈
  PF.map-× PF.ι₂ e
map-id-ι₂ =
  PFEq.≈-trans PFEq.map-×-C
    (PFEq.map-×-cong PFEq.C-idˡ PFEq.C-idʳ)

step-ι₁-right :
  ∀ {Γ Δ A : PF.TY PF.HO}
  {h : Γ PF.→ᴾ A PF.`⇒ SystemT.Natᴴ PF.`⇒ A}
  {z : Γ PF.→ᴾ A}
  {e : Δ PF.→ᴾ Γ} →
  PF.C (PF.C (stepPF h z) (PF.map-× PF.id e))
    (PF.map-× PF.ι₁ PF.id)
    PFEq.≈
  baseStepPF (PF.C z e)
step-ι₁-right {h = h} {z = z} {e = e} =
  PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
    (PFEq.≈-trans
      (PFEq.C-cong PFEq.≈-refl map-id-ι₁)
      step-ι₁-param)
  where
  step-ι₁-param :
    PF.C (stepPF h z) (PF.map-× PF.ι₁ e)
      PFEq.≈
    baseStepPF (PF.C z e)
  step-ι₁-param =
    PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
      (PFEq.≈-trans
        (PFEq.C-cong PFEq.≈-refl dist-map-ι₁-right)
        (PFEq.≈-trans PFEq.C-assoc
          (PFEq.≈-trans
            (PFEq.C-cong PFEq.+-β₁ PFEq.≈-refl)
            (PFEq.≈-sym baseStep-natural))))

step-ι₂-right :
  ∀ {Γ Δ A : PF.TY PF.HO}
  {h : Γ PF.→ᴾ A PF.`⇒ SystemT.Natᴴ PF.`⇒ A}
  {z : Γ PF.→ᴾ A}
  {e : Δ PF.→ᴾ Γ} →
  PF.C (PF.C (stepPF h z) (PF.map-× PF.id e))
    (PF.map-× PF.ι₂ PF.id)
    PFEq.≈
  succStepPF (PF.C h e)
step-ι₂-right {h = h} {z = z} {e = e} =
  PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
    (PFEq.≈-trans
      (PFEq.C-cong PFEq.≈-refl map-id-ι₂)
      step-ι₂-param)
  where
  step-ι₂-param :
    PF.C (stepPF h z) (PF.map-× PF.ι₂ e)
      PFEq.≈
    succStepPF (PF.C h e)
  step-ι₂-param =
    PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
      (PFEq.≈-trans
        (PFEq.C-cong PFEq.≈-refl dist-map-ι₂-right)
        (PFEq.≈-trans PFEq.C-assoc
          (PFEq.≈-trans
            (PFEq.C-cong PFEq.+-β₂ PFEq.≈-refl)
            (PFEq.≈-sym succStep-natural))))

step-naturalPF :
  ∀ {Γ Δ A : PF.TY PF.HO}
  {h : Γ PF.→ᴾ A PF.`⇒ SystemT.Natᴴ PF.`⇒ A}
  {z : Γ PF.→ᴾ A}
  {e : Δ PF.→ᴾ Γ} →
  stepPF (PF.C h e) (PF.C z e)
    PFEq.≈
  PF.C (stepPF h z) (PF.map-× PF.id e)
step-naturalPF {h = h} {z = z} {e = e} =
  PFEq.theta-lam-ext
    (PFEq.≈-trans (PFEq.≈-sym PFEq.+-η)
      (PFEq.≈-trans
        (PFEq.`case-cong branch₁ branch₂)
        PFEq.+-η))
  where
  branch₁ :
    PF.C (PF.lam (stepPF (PF.C h e) (PF.C z e))) PF.ι₁
      PFEq.≈
    PF.C (PF.lam (PF.C (stepPF h z) (PF.map-× PF.id e))) PF.ι₁
  branch₁ =
    PFEq.≈-trans
      (PFEq.≈-trans PFEq.lam-precomp
        (PFEq.lam-cong step-ι₁))
      (PFEq.≈-sym
        (PFEq.≈-trans PFEq.lam-precomp
          (PFEq.lam-cong step-ι₁-right)))

  branch₂ :
    PF.C (PF.lam (stepPF (PF.C h e) (PF.C z e))) PF.ι₂
      PFEq.≈
    PF.C (PF.lam (PF.C (stepPF h z) (PF.map-× PF.id e))) PF.ι₂
  branch₂ =
    PFEq.≈-trans
      (PFEq.≈-trans PFEq.lam-precomp
        (PFEq.lam-cong step-ι₂))
      (PFEq.≈-sym
        (PFEq.≈-trans PFEq.lam-precomp
          (PFEq.lam-cong step-ι₂-right)))


prec-precompPF :
  ∀ {Γ Δ A : PF.TY PF.HO}
  {h : Γ PF.→ᴾ A PF.`⇒ SystemT.Natᴴ PF.`⇒ A}
  {z : Γ PF.→ᴾ A}
  {n : Γ PF.→ᴾ SystemT.Natᴴ}
  {e : Δ PF.→ᴾ Γ} →
  precPF (PF.C h e) (PF.C z e) (PF.C n e)
    PFEq.≈
  PF.C (precPF h z n) e
prec-precompPF {h = h} {z = z} {n = n} {e = e} =
  PFEq.≈-trans
    (PFEq.C-cong
      (PFEq.Pr-cong step-naturalPF)
      PFEq.≈-refl)
    (Pr-precomp-parameter PFEq.≈-refl)

rename-preserves :
  ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {A}
  (ρ : Ren Γ Δ) (t : Exp Γ A) →
  toPRHO (rename {Γ = Γ} {Δ = Δ} ρ t)
    PFEq.≈
  PF.C (toPRHO t) (renEnv {Γ = Γ} {Δ = Δ} ρ)
rename-preserves ρ (Source.Var i) =
  PFEq.≈-sym (lookup-renEnv ρ i)
rename-preserves {Γ = Γ} {Δ = Δ} ρ (Source.Lam t) =
  PFEq.≈-trans
    (PFEq.lam-cong
      (rename-preserves
        (liftRen {Γ = Γ} {Δ = Δ} ρ) t))
    (PFEq.≈-trans
      (PFEq.lam-cong
        (PFEq.C-cong PFEq.≈-refl
          (renEnv-lift {Γ = Γ} {Δ = Δ} ρ)))
      (PFEq.≈-sym PFEq.lam-precomp))
rename-preserves ρ Source.CZero = zero-natural
rename-preserves ρ Source.Suc = suc-natural
rename-preserves ρ (Source.App f x) =
  PFEq.≈-trans
    (app-congPF (rename-preserves ρ f) (rename-preserves ρ x))
    (PFEq.≈-sym app-precomp)
rename-preserves {Γ = Γ} ρ (Source.Nat n) =
  PFEq.≈-trans (PFEq.≈-sym (numeral-toPRHO n))
    (PFEq.≈-trans (numeral-natural n)
      (PFEq.C-cong (numeral-toPRHO {Γ = Γ} n) PFEq.≈-refl))
rename-preserves {Γ = Γ} {Δ = Δ} ρ (Source.PrecT h z n) =
  PFEq.≈-trans
    (prec-congPF
      (rename-preserves ρ h)
      (rename-preserves ρ z)
      (rename-preserves ρ n))
    prec-precompPF

weaken-preserves :
  ∀ {n} {Γ : Ctx n} {A B} (t : Exp Γ A) →
  toPRHO (weaken {A = A} {B = B} t)
    PFEq.≈
  PF.C (toPRHO t) PF.π₁
weaken-preserves {Γ = Γ} {B = B} t =
  PFEq.≈-trans
    (rename-preserves {Γ = Γ} {Δ = B ∷ Γ} weakenRen t)
    (PFEq.C-cong PFEq.≈-refl renEnv-weaken)

subEnv-tail-lift : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {A}
  (σ : Sub Γ Δ) →
  subEnv {Γ = Γ} {Δ = A ∷ Δ}
    (λ i → liftSub {Γ = Γ} {Δ = Δ} {A = A} σ (Fin.suc i))
    PFEq.≈ PF.C (subEnv {Γ = Γ} {Δ = Δ} σ) PF.π₁
subEnv-tail-lift {Γ = []} σ =
  PFEq.≈-sym PFEq.𝟙-unique
subEnv-tail-lift {Γ = B ∷ Γ} {Δ = Δ} {A = A} σ =
  PFEq.≈-trans
    (PFEq.`#-cong
      (subEnv-tail-lift {Γ = Γ} {Δ = Δ} {A = A}
        (λ i → σ (Fin.suc i)))
      (weaken-preserves (σ Fin.zero)))
    (PFEq.≈-sym PFEq.C-#)

subEnv-lift : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {A}
  (σ : Sub Γ Δ) →
  subEnv {Γ = A ∷ Γ} {Δ = A ∷ Δ}
    (liftSub {Γ = Γ} {Δ = Δ} {A = A} σ)
    PFEq.≈ PF.map-× (subEnv {Γ = Γ} {Δ = Δ} σ) PF.id
subEnv-lift {Γ = Γ} {Δ = Δ} {A = A} σ =
  PFEq.`#-cong
    (subEnv-tail-lift {Γ = Γ} {Δ = Δ} {A = A} σ)
    (PFEq.≈-sym PFEq.C-idˡ)

subEnv-weaken-vars : ∀ {n} {Γ : Ctx n} {A} →
  subEnv {Γ = Γ} {Δ = A ∷ Γ} (λ i → Source.Var (Fin.suc i))
    PFEq.≈ PF.π₁
subEnv-weaken-vars {Γ = []} =
  PFEq.≈-sym PFEq.𝟙-unique
subEnv-weaken-vars {Γ = B ∷ Γ} {A = A} =
  PFEq.≈-trans
    (PFEq.`#-cong
      (PFEq.≈-trans
        (subEnv-tail-lift {Γ = Γ} {Δ = B ∷ Γ} {A = A}
          (λ i → Source.Var (Fin.suc i)))
        (PFEq.C-cong subEnv-weaken-vars PFEq.≈-refl))
      PFEq.≈-refl)
    (PFEq.≈-trans
      (PFEq.≈-sym PFEq.C-#)
      (PFEq.≈-trans
        (PFEq.C-cong PFEq.pair-id PFEq.≈-refl)
        PFEq.C-idˡ))

subEnv-id : ∀ {n} {Γ : Ctx n} →
  subEnv {Γ = Γ} {Δ = Γ} (λ i → Source.Var i) PFEq.≈ PF.id
subEnv-id {Γ = []} =
  PFEq.≈-sym PFEq.𝟙-unique
subEnv-id {Γ = A ∷ Γ} =
  PFEq.≈-trans
    (PFEq.`#-cong subEnv-weaken-vars PFEq.≈-refl)
    PFEq.pair-id

subEnv-cong : ∀ {m n} {Γ : Ctx n} {Δ : Ctx m}
  {σ τ : Sub Γ Δ} →
  ((i : Fin.Fin n) → toPRHO (σ i) PFEq.≈ toPRHO (τ i)) →
  subEnv {Γ = Γ} {Δ = Δ} σ PFEq.≈ subEnv {Γ = Γ} {Δ = Δ} τ
subEnv-cong {Γ = []} pointwise = PFEq.≈-refl
subEnv-cong {Γ = A ∷ Γ} pointwise =
  PFEq.`#-cong
    (subEnv-cong (λ i → pointwise (Fin.suc i)))
    (pointwise Fin.zero)

subst-preserves :
  ∀ {m n} {Γ : Ctx n} {Δ : Ctx m} {A}
  (σ : Sub Γ Δ) (t : Exp Γ A) →
  toPRHO (subst {Γ = Γ} {Δ = Δ} σ t)
    PFEq.≈
  PF.C (toPRHO t) (subEnv {Γ = Γ} {Δ = Δ} σ)
subst-preserves σ (Source.Var i) =
  PFEq.≈-sym (lookup-subEnv σ i)
subst-preserves {Γ = Γ} {Δ = Δ} σ (Source.Lam t) =
  PFEq.≈-trans
    (PFEq.lam-cong
      (subst-preserves
        (liftSub {Γ = Γ} {Δ = Δ} σ) t))
    (PFEq.≈-trans
      (PFEq.lam-cong
        (PFEq.C-cong PFEq.≈-refl
          (subEnv-lift {Γ = Γ} {Δ = Δ} σ)))
      (PFEq.≈-sym PFEq.lam-precomp))
subst-preserves σ Source.CZero = zero-natural
subst-preserves σ Source.Suc = suc-natural
subst-preserves σ (Source.App f x) =
  PFEq.≈-trans
    (app-congPF (subst-preserves σ f) (subst-preserves σ x))
    (PFEq.≈-sym app-precomp)
subst-preserves {Γ = Γ} σ (Source.Nat n) =
  PFEq.≈-trans (PFEq.≈-sym (numeral-toPRHO n))
    (PFEq.≈-trans (numeral-natural n)
      (PFEq.C-cong (numeral-toPRHO {Γ = Γ} n) PFEq.≈-refl))
subst-preserves {Γ = Γ} {Δ = Δ} σ (Source.PrecT h z n) =
  PFEq.≈-trans
    (prec-congPF
      (subst-preserves σ h)
      (subst-preserves σ z)
      (subst-preserves σ n))
    prec-precompPF

singleSub-env : ∀ {n} {Γ : Ctx n} {A}
  (u : Exp Γ A) →
  subEnv {Γ = A ∷ Γ} {Δ = Γ} (singleSub u)
    PFEq.≈
  PF.`# PF.id (toPRHO u)
singleSub-env u =
  PFEq.`#-cong subEnv-id PFEq.≈-refl

app-βPF :
  ∀ {Γ A B : PF.TY PF.HO}
  {body : Γ PF.`× A PF.→ᴾ B}
  {x : Γ PF.→ᴾ A} →
  appPF (PF.lam body) x PFEq.≈ PF.C body (PF.`# PF.id x)
app-βPF =
  PFEq.≈-trans
    (PFEq.C-cong PFEq.≈-refl
      (PFEq.≈-sym
        (PFEq.≈-trans PFEq.map-×-#
          (PFEq.`#-cong PFEq.C-idʳ PFEq.C-idˡ))))
    (PFEq.≈-trans PFEq.C-assoc
      (PFEq.C-cong PFEq.⇒-β PFEq.≈-refl))

app-ηPF :
  ∀ {n} {Γ : Ctx n} {A B}
  (f : Exp Γ (A Source.⇒ B)) →
  toPRHO (Source.Lam (Source.App (weaken f) (Source.Var Fin.zero)))
    PFEq.≈
  toPRHO f
app-ηPF f =
  PFEq.≈-trans
    (PFEq.lam-cong
      (app-congPF (weaken-preserves f) PFEq.≈-refl))
    (PFEq.≈-trans
      (PFEq.lam-cong
        (PFEq.C-cong PFEq.≈-refl
          (PFEq.`#-cong PFEq.≈-refl (PFEq.≈-sym PFEq.C-idˡ))))
      PFEq.⇒-η)

app-βₛ-preserves :
  ∀ {n} {Γ : Ctx n} {A B}
  (t : Exp (A ∷ Γ) B) (u : Exp Γ A) →
  toPRHO (Source.App (Source.Lam t) u)
    PFEq.≈
  toPRHO (subst0 u t)
app-βₛ-preserves t u =
  PFEq.≈-trans app-βPF
    (PFEq.≈-sym
      (PFEq.≈-trans
        (subst-preserves (singleSub u) t)
        (PFEq.C-cong PFEq.≈-refl (singleSub-env u))))

zeroLayer : ∀ {Γ A : PF.TY PF.HO} →
  Γ PF.→ᴾ SystemT.NatF PF.[ A ]
zeroLayer = PF.C PF.ι₁ PF.`⊤

zeroInput-factor :
  ∀ {Γ A : PF.TY PF.HO} →
  PF.`# (zeroLayer {Γ = Γ} {A = A}) PF.id
    PFEq.≈
  PF.C (PF.map-× PF.ι₁ PF.id) (PF.`# PF.`⊤ PF.id)
zeroInput-factor =
  PFEq.≈-sym
    (PFEq.≈-trans PFEq.map-×-#
      (PFEq.`#-cong PFEq.≈-refl PFEq.C-idˡ))

strengthNat-zero :
  ∀ {Γ : PF.TY PF.HO} →
  PF.C (PF.strengthᶜ {T = SystemT.Natᴴ} {U = Γ} SystemT.NatF-structural)
    (PF.`# zeroLayer PF.id)
    PFEq.≈
  zeroLayer {Γ = Γ} {A = SystemT.Natᴴ PF.`× Γ}
strengthNat-zero {Γ = Γ} =
  PFEq.≈-trans
    (PFEq.C-cong PFEq.≈-refl zeroInput-factor)
    (PFEq.≈-trans PFEq.C-assoc
      (PFEq.≈-trans
        (PFEq.C-cong strength-zero-branch PFEq.≈-refl)
        zero-branch-input))
  where
  strength-zero-branch :
    PF.C (PF.strengthᶜ {T = SystemT.Natᴴ} {U = Γ} SystemT.NatF-structural)
      (PF.map-× PF.ι₁ PF.id)
      PFEq.≈
    PF.C PF.ι₁ PF.π₁
  strength-zero-branch =
    PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
      (PFEq.≈-trans
        (PFEq.C-cong PFEq.≈-refl PFEq.dist-map-ι₁)
        PFEq.+-β₁)

  zero-branch-input :
    PF.C (PF.C PF.ι₁ PF.π₁) (PF.`# PF.`⊤ PF.id)
      PFEq.≈
    zeroLayer
  zero-branch-input =
    PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
      (PFEq.C-cong PFEq.≈-refl PFEq.×-β₁)

fmapNat-zero :
  ∀ {Γ A B : PF.TY PF.HO}
  {f : A PF.→ᴾ B} →
  PF.C (PF.fmapᶜ SystemT.NatF-structural f) (zeroLayer {Γ = Γ} {A = A})
    PFEq.≈
  zeroLayer {Γ = Γ} {A = B}
fmapNat-zero =
  PFEq.≈-trans PFEq.C-assoc
    (PFEq.≈-trans
      (PFEq.C-cong PFEq.+-β₁ PFEq.≈-refl)
      (PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
        (PFEq.C-cong PFEq.≈-refl PFEq.C-idˡ)))

paraZero-layer :
  ∀ {Γ A : PF.TY PF.HO}
  {step : (SystemT.NatF PF.[ A PF.`× SystemT.Natᴴ ]) PF.`× Γ PF.→ᴾ A} →
  PF.C
    (PF.fmapᶜ SystemT.NatF-structural
      (PF.`# (PF.Pr step) PF.π₁))
    (PF.C
      (PF.strengthᶜ {T = SystemT.Natᴴ} {U = Γ} SystemT.NatF-structural)
      (PF.`# zeroLayer PF.id))
    PFEq.≈
  zeroLayer {Γ = Γ} {A = A PF.`× SystemT.Natᴴ}
paraZero-layer =
  PFEq.≈-trans
    (PFEq.C-cong PFEq.≈-refl strengthNat-zero)
    fmapNat-zero

step-zero-input :
  ∀ {Γ A : PF.TY PF.HO}
  {h : Γ PF.→ᴾ A PF.`⇒ SystemT.Natᴴ PF.`⇒ A}
  {z : Γ PF.→ᴾ A} →
  PF.C (stepPF h z) (PF.`# zeroLayer PF.id) PFEq.≈ z
step-zero-input {h = h} {z = z} =
  PFEq.≈-trans
    (PFEq.C-cong PFEq.≈-refl zeroInput-factor)
    (PFEq.≈-trans PFEq.C-assoc
      (PFEq.≈-trans
        (PFEq.C-cong step-ι₁ PFEq.≈-refl)
        base-input))
  where
  base-input :
    PF.C (baseStepPF z) (PF.`# PF.`⊤ PF.id) PFEq.≈ z
  base-input =
    PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
      (PFEq.≈-trans
        (PFEq.C-cong PFEq.≈-refl PFEq.×-β₂)
        PFEq.C-idʳ)

prec-zeroPF :
  ∀ {Γ A : PF.TY PF.HO}
  {h : Γ PF.→ᴾ A PF.`⇒ SystemT.Natᴴ PF.`⇒ A}
  {z : Γ PF.→ᴾ A} →
  precPF h z zeroPF PFEq.≈ z
prec-zeroPF {h = h} {z = z} =
  PFEq.≈-trans
    (PFEq.Pr-βᶜ SystemT.NatF-structural)
    (PFEq.≈-trans
      (PFEq.C-cong PFEq.≈-refl
        (PFEq.`#-cong paraZero-layer PFEq.≈-refl))
      step-zero-input)

suc-βPF :
  ∀ {Γ : PF.TY PF.HO} {k : Γ PF.→ᴾ SystemT.Natᴴ} →
  appPF sucPF k PFEq.≈ PF.C (PF.con {G = SystemT.NatF}) (PF.C PF.ι₂ k)
suc-βPF =
  PFEq.≈-trans app-βPF
    (PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
      (PFEq.C-cong PFEq.≈-refl
        (PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
          (PFEq.C-cong PFEq.≈-refl PFEq.×-β₂))))

sucInput-factor :
  ∀ {Γ L A : PF.TY PF.HO} {r : Γ PF.→ᴾ A} →
  PF.`# (PF.C (PF.ι₂ {U = L}) r) PF.id
    PFEq.≈
  PF.C (PF.map-× (PF.ι₂ {U = L}) PF.id) (PF.`# r PF.id)
sucInput-factor =
  PFEq.≈-sym
    (PFEq.≈-trans PFEq.map-×-#
      (PFEq.`#-cong PFEq.≈-refl PFEq.C-idˡ))

strengthNat-suc :
  ∀ {Γ : PF.TY PF.HO} {k : Γ PF.→ᴾ SystemT.Natᴴ} →
  PF.C (PF.strengthᶜ {T = SystemT.Natᴴ} {U = Γ} SystemT.NatF-structural)
    (PF.`# (PF.C PF.ι₂ k) PF.id)
    PFEq.≈
  PF.C PF.ι₂ (PF.`# k PF.id)
strengthNat-suc {Γ = Γ} {k = k} =
  PFEq.≈-trans
    (PFEq.C-cong PFEq.≈-refl (sucInput-factor {L = PF.`𝟙}))
    (PFEq.≈-trans PFEq.C-assoc
      (PFEq.≈-trans
        (PFEq.C-cong strength-suc-branch PFEq.≈-refl)
        suc-branch-input))
  where
  strength-suc-branch :
    PF.C (PF.strengthᶜ {T = SystemT.Natᴴ} {U = Γ} SystemT.NatF-structural)
      (PF.map-× PF.ι₂ PF.id)
      PFEq.≈
    PF.C PF.ι₂ PF.id
  strength-suc-branch =
    PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
      (PFEq.≈-trans
        (PFEq.C-cong PFEq.≈-refl PFEq.dist-map-ι₂)
        PFEq.+-β₂)

  suc-branch-input :
    PF.C (PF.C PF.ι₂ PF.id) (PF.`# k PF.id)
      PFEq.≈
    PF.C PF.ι₂ (PF.`# k PF.id)
  suc-branch-input =
    PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
      (PFEq.C-cong PFEq.≈-refl PFEq.C-idˡ)

fmapNat-suc :
  ∀ {Γ A B : PF.TY PF.HO}
  {f : A PF.→ᴾ B}
  {x : Γ PF.→ᴾ A} →
  PF.C (PF.fmapᶜ SystemT.NatF-structural f) (PF.C PF.ι₂ x)
    PFEq.≈
  PF.C PF.ι₂ (PF.C f x)
fmapNat-suc =
  PFEq.≈-trans PFEq.C-assoc
    (PFEq.≈-trans
      (PFEq.C-cong PFEq.+-β₂ PFEq.≈-refl)
      (PFEq.≈-sym PFEq.C-assoc))

paraSuc-layer :
  ∀ {Γ A : PF.TY PF.HO}
  {step : (SystemT.NatF PF.[ A PF.`× SystemT.Natᴴ ]) PF.`× Γ PF.→ᴾ A}
  {k : Γ PF.→ᴾ SystemT.Natᴴ} →
  PF.C
    (PF.fmapᶜ SystemT.NatF-structural
      (PF.`# (PF.Pr step) PF.π₁))
    (PF.C
      (PF.strengthᶜ {T = SystemT.Natᴴ} {U = Γ} SystemT.NatF-structural)
      (PF.`# (PF.C PF.ι₂ k) PF.id))
    PFEq.≈
  PF.C PF.ι₂ (PF.`# (PF.C (PF.Pr step) (PF.`# k PF.id)) k)
paraSuc-layer =
  PFEq.≈-trans
    (PFEq.C-cong PFEq.≈-refl strengthNat-suc)
    (PFEq.≈-trans fmapNat-suc
      (PFEq.C-cong PFEq.≈-refl
        (PFEq.≈-trans PFEq.C-#
          (PFEq.`#-cong PFEq.≈-refl PFEq.×-β₁))))

succStep-input :
  ∀ {Γ A : PF.TY PF.HO}
  {h : Γ PF.→ᴾ A PF.`⇒ SystemT.Natᴴ PF.`⇒ A}
  {rec : Γ PF.→ᴾ A}
  {k : Γ PF.→ᴾ SystemT.Natᴴ} →
  PF.C (succStepPF h) (PF.`# (PF.`# rec k) PF.id)
    PFEq.≈
  appPF (appPF h rec) k
succStep-input {h = h} {rec = rec} {k = k} =
  PFEq.≈-trans app-precomp
    (app-congPF inner-input counter-input)
  where
  function-input :
    PF.C (PF.C h PF.π₂) (PF.`# (PF.`# rec k) PF.id) PFEq.≈ h
  function-input =
    PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
      (PFEq.≈-trans
        (PFEq.C-cong PFEq.≈-refl PFEq.×-β₂)
        PFEq.C-idʳ)

  recursive-input :
    PF.C (PF.C PF.π₁ PF.π₁) (PF.`# (PF.`# rec k) PF.id)
      PFEq.≈ rec
  recursive-input =
    PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
      (PFEq.≈-trans
        (PFEq.C-cong PFEq.≈-refl PFEq.×-β₁)
        PFEq.×-β₁)

  inner-input :
    PF.C (appPF (PF.C h PF.π₂) (PF.C PF.π₁ PF.π₁))
      (PF.`# (PF.`# rec k) PF.id)
      PFEq.≈
    appPF h rec
  inner-input =
    PFEq.≈-trans app-precomp
      (app-congPF function-input recursive-input)

  counter-input :
    PF.C (PF.C PF.π₂ PF.π₁) (PF.`# (PF.`# rec k) PF.id)
      PFEq.≈ k
  counter-input =
    PFEq.≈-trans (PFEq.≈-sym PFEq.C-assoc)
      (PFEq.≈-trans
        (PFEq.C-cong PFEq.≈-refl PFEq.×-β₁)
        PFEq.×-β₂)

step-suc-input :
  ∀ {Γ A : PF.TY PF.HO}
  {h : Γ PF.→ᴾ A PF.`⇒ SystemT.Natᴴ PF.`⇒ A}
  {z : Γ PF.→ᴾ A}
  {rec : Γ PF.→ᴾ A}
  {k : Γ PF.→ᴾ SystemT.Natᴴ} →
  PF.C (stepPF h z) (PF.`# (PF.C PF.ι₂ (PF.`# rec k)) PF.id)
    PFEq.≈
  appPF (appPF h rec) k
step-suc-input =
  PFEq.≈-trans
    (PFEq.C-cong PFEq.≈-refl (sucInput-factor {L = PF.`𝟙}))
    (PFEq.≈-trans PFEq.C-assoc
      (PFEq.≈-trans
        (PFEq.C-cong step-ι₂ PFEq.≈-refl)
        succStep-input))

prec-sucPF :
  ∀ {Γ A : PF.TY PF.HO}
  {h : Γ PF.→ᴾ A PF.`⇒ SystemT.Natᴴ PF.`⇒ A}
  {z : Γ PF.→ᴾ A}
  {k : Γ PF.→ᴾ SystemT.Natᴴ} →
  precPF h z (appPF sucPF k)
    PFEq.≈
  appPF (appPF h (precPF h z k)) k
prec-sucPF {h = h} {z = z} {k = k} =
  PFEq.≈-trans
    (PFEq.C-cong PFEq.≈-refl
      (PFEq.`#-cong suc-βPF PFEq.≈-refl))
    (PFEq.≈-trans
      (PFEq.Pr-βᶜ SystemT.NatF-structural)
      (PFEq.≈-trans
        (PFEq.C-cong PFEq.≈-refl
          (PFEq.`#-cong paraSuc-layer PFEq.≈-refl))
        step-suc-input))

preserves : ∀ {n} {Γ : Ctx n} {A} {t u : Exp Γ A} →
  t ≈ₛ u → toPRHO t PFEq.≈ toPRHO u
preserves reflₛ = PFEq.≈-refl
preserves (symₛ equation) = PFEq.≈-sym (preserves equation)
preserves (transₛ first second) =
  PFEq.≈-trans (preserves first) (preserves second)
preserves (Lam-congₛ equation) =
  PFEq.lam-cong (preserves equation)
preserves (App-congₛ f x) =
  app-congPF (preserves f) (preserves x)
preserves (PrecT-congₛ h z n) =
  prec-congPF (preserves h) (preserves z) (preserves n)
preserves (subst-congₛ {σ = σ} {τ = τ} {t = t} {u = u} equation pointwise) =
  PFEq.≈-trans (subst-preserves σ t)
    (PFEq.≈-trans
      (PFEq.C-cong (preserves equation)
        (subEnv-cong (λ i → preserves (pointwise i))))
      (PFEq.≈-sym (subst-preserves τ u)))
preserves (⇒-βₛ t u) = app-βₛ-preserves t u
preserves (⇒-ηₛ f) = app-ηPF f
preserves (PrecT-zeroₛ h z) = prec-zeroPF
preserves (PrecT-sucₛ h z k) = prec-sucPF
preserves (PrecT-nat-zeroₛ h z) = prec-zeroPF
preserves (PrecT-nat-sucₛ h z k) = prec-sucPF

contextual-equations-preserved : ∀ {Γ A}
  {t u : Γ Ctx.⊢ A} →
  t CtxEq.≈ u →
  Ctx⇔PF.compile t PFEq.≈ Ctx⇔PF.compile u
contextual-equations-preserved equation =
  Ctx⇔PF.compile-sound equation
