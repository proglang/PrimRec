{-# OPTIONS --safe #-}

module Core.Instances.SystemT where

import Data.Fin as Fin
import Data.Nat as Nat
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import System-T as ST
open import Core.Types
import Core.Contextual.PRHO as Ctx
import Core.Contextual.Equations.PRHO as CtxEq
import Core.PRHO as PF
import Core.Equations.PRHO as PFEq
import Core.Models.PRHO as Model
import Core.Models.PRHOSet as SetModel
import Core.Translations.ContextualPRHO as Ctx⇔PF

----------------------------------------------------------------------
-- Translation of the safe legacy System-T syntax into the reusable
-- contextual and point-free PR-HO core.
----------------------------------------------------------------------

STy : Set
STy = ST.Ty

Ctx : Nat.ℕ → Set
Ctx = ST.Ctx

Exp : ∀ {n : Nat.ℕ} → Ctx n → STy → Set
Exp = ST.Exp

----------------------------------------------------------------------
-- Type and context translation.
----------------------------------------------------------------------

NatF : Ty HO 1
NatF = `𝟙 `+ ` Fin.zero

Natᴴ : TY HO
Natᴴ = ind NatF

⟦_⟧ᵀ : STy → TY HO
⟦ ST.TyNat ⟧ᵀ = Natᴴ
⟦ ST._⇒_ A B ⟧ᵀ = ⟦ A ⟧ᵀ `⇒ ⟦ B ⟧ᵀ

⟦_⟧ᶜ : ∀ {n : Nat.ℕ} → Ctx n → TY HO
⟦ [] ⟧ᶜ = `𝟙
⟦ A ∷ Γ ⟧ᶜ = ⟦ Γ ⟧ᶜ `× ⟦ A ⟧ᵀ

lookupᵀ : ∀ {n : Nat.ℕ} {Γ : Ctx n}
  → (i : Fin.Fin n)
  → ⟦ Γ ⟧ᶜ Ctx.⊢ ⟦ lookup Γ i ⟧ᵀ
lookupᵀ {Γ = A ∷ Γ} Fin.zero = Ctx.snd
lookupᵀ {Γ = A ∷ Γ} (Fin.suc i) = Ctx.cut (lookupᵀ {Γ = Γ} i) Ctx.fst

----------------------------------------------------------------------
-- Contextual PR-HO terms implementing the System T constants.
----------------------------------------------------------------------

app : ∀ {Γ A B : TY HO}
  → Γ Ctx.⊢ A `⇒ B
  → Γ Ctx.⊢ A
  → Γ Ctx.⊢ B
app f x = Ctx.cut Ctx.eval (Ctx.pair f x)

zeroᴴ : ∀ {Γ : TY HO} → Γ Ctx.⊢ Natᴴ
zeroᴴ = Ctx.cut Ctx.con (Ctx.cut Ctx.inl Ctx.unit)

sucᴴ : ∀ {Γ : TY HO} → Γ Ctx.⊢ Natᴴ `⇒ Natᴴ
sucᴴ = Ctx.curry (Ctx.cut Ctx.con (Ctx.cut Ctx.inr Ctx.snd))

numeral : ∀ {Γ : TY HO} → Nat.ℕ → Γ Ctx.⊢ Natᴴ
numeral Nat.zero = zeroᴴ
numeral (Nat.suc n) = app sucᴴ (numeral n)

stepᴴ : ∀ {Γ A : TY HO}
  → Γ Ctx.⊢ A `⇒ Natᴴ `⇒ A
  → Γ Ctx.⊢ A
  → (NatF [ A `× Natᴴ ]) `× Γ Ctx.⊢ A
stepᴴ {Γ} {A} h z =
  Ctx.cut
    (Ctx.cases base succ)
    (Ctx.dist-+-× {A = `𝟙} {B = A `× Natᴴ} {C = Γ})
  where
    base : `𝟙 `× Γ Ctx.⊢ A
    base = Ctx.cut z Ctx.snd

    succ : (A `× Natᴴ) `× Γ Ctx.⊢ A
    succ =
      app
        (app (Ctx.cut h Ctx.snd)
             (Ctx.cut (Ctx.fst {A = A} {B = Natᴴ})
               (Ctx.fst {A = A `× Natᴴ} {B = Γ})))
        (Ctx.cut (Ctx.snd {A = A} {B = Natᴴ})
          (Ctx.fst {A = A `× Natᴴ} {B = Γ}))

precᴴ : ∀ {Γ A : TY HO}
  → Γ Ctx.⊢ A `⇒ Natᴴ `⇒ A
  → Γ Ctx.⊢ A
  → Γ Ctx.⊢ Natᴴ
  → Γ Ctx.⊢ A
precᴴ {Γ} h z n =
  Ctx.cut (Ctx.prec (stepᴴ h z)) (Ctx.pair n Ctx.var)

----------------------------------------------------------------------
-- System T elaboration into contextual PR-HO and then point-free PR-HO.
----------------------------------------------------------------------

elab : ∀ {n : Nat.ℕ} {Γ : Ctx n} {A : STy}
  → Exp Γ A
  → ⟦ Γ ⟧ᶜ Ctx.⊢ ⟦ A ⟧ᵀ
elab (ST.Var i) = lookupᵀ i
elab (ST.Lam t) = Ctx.curry (elab t)
elab ST.CZero = zeroᴴ
elab ST.Suc = sucᴴ
elab (ST.App f x) = app (elab f) (elab x)
elab (ST.Nat n) = numeral n
elab (ST.PrecT h z n) = precᴴ (elab h) (elab z) (elab n)

toPRHO : ∀ {n : Nat.ℕ} {Γ : Ctx n} {A : STy}
  → Exp Γ A
  → ⟦ Γ ⟧ᶜ PF.→ᴾ ⟦ A ⟧ᵀ
toPRHO t = Ctx⇔PF.compile (elab t)

toPRHO-factors : ∀ {n : Nat.ℕ} {Γ : Ctx n} {A : STy}
  → (t : Exp Γ A)
  → toPRHO t ≡ Ctx⇔PF.compile (elab t)
toPRHO-factors t = refl

toPRHO-reify : ∀ {n : Nat.ℕ} {Γ : Ctx n} {A : STy}
  → (t : Exp Γ A)
  → Ctx⇔PF.reify (toPRHO t) ≡ elab t
toPRHO-reify t = Ctx⇔PF.reify-compile (elab t)

toPRHO-reify≈ : ∀ {n : Nat.ℕ} {Γ : Ctx n} {A : STy}
  → (t : Exp Γ A)
  → Ctx⇔PF.reify (toPRHO t) CtxEq.≈ elab t
toPRHO-reify≈ t = Ctx⇔PF.reify-compile≈ (elab t)

contextual-equations-preserved : ∀ {Γ A : TY HO}
  {t u : Γ Ctx.⊢ A}
  → t CtxEq.≈ u
  → Ctx⇔PF.compile t PFEq.≈ Ctx⇔PF.compile u
contextual-equations-preserved = Ctx⇔PF.compile-sound

----------------------------------------------------------------------
-- Model-level source semantics and semantic correctness.
--
-- This is the System-T analogue of the instance preservation theorems for
-- naturals, words, trees, and many-sorted signatures: interpreting the
-- translated PR-HO arrow agrees with a direct structural denotation of the
-- source System-T term in any PR-HO model.
----------------------------------------------------------------------

module Semantics {ℓ : Level} (M : Model.Model ℓ) where
  open Model.Model M

  appᴹ : ∀ {Γ A B : TY HO}
    → Γ ⇒ᴹ A `⇒ B
    → Γ ⇒ᴹ A
    → Γ ⇒ᴹ B
  appᴹ f x = Cᴹ applyᴹ (pairᴹ f x)

  app-congᴹ : ∀ {Γ A B : TY HO}
    {f f′ : Γ ⇒ᴹ A `⇒ B}
    {x x′ : Γ ⇒ᴹ A}
    → f ≈ᴹ f′
    → x ≈ᴹ x′
    → appᴹ f x ≈ᴹ appᴹ f′ x′
  app-congᴹ f≈ x≈ = C-congᴹ ≈-reflᴹ (pair-congᴹ f≈ x≈)

  zeroᴹ : ∀ {Γ : TY HO} → Γ ⇒ᴹ Natᴴ
  zeroᴹ = Cᴹ conᴹ (Cᴹ ι₁ᴹ ⊤ᴹ)

  sucᴹ : ∀ {Γ : TY HO} → Γ ⇒ᴹ Natᴴ `⇒ Natᴴ
  sucᴹ = lamᴹ (Cᴹ conᴹ (Cᴹ ι₂ᴹ π₂ᴹ))

  numeralᴹ : ∀ {Γ : TY HO} → Nat.ℕ → Γ ⇒ᴹ Natᴴ
  numeralᴹ Nat.zero = zeroᴹ
  numeralᴹ (Nat.suc n) = appᴹ sucᴹ (numeralᴹ n)

  lookupᴹ : ∀ {n : Nat.ℕ} {Γ : Ctx n}
    → (i : Fin.Fin n)
    → ⟦ Γ ⟧ᶜ ⇒ᴹ ⟦ lookup Γ i ⟧ᵀ
  lookupᴹ {Γ = A ∷ Γ} Fin.zero = π₂ᴹ
  lookupᴹ {Γ = A ∷ Γ} (Fin.suc i) = Cᴹ (lookupᴹ {Γ = Γ} i) π₁ᴹ

  stepᴹ : ∀ {Γ A : TY HO}
    → Γ ⇒ᴹ A `⇒ Natᴴ `⇒ A
    → Γ ⇒ᴹ A
    → (NatF [ A `× Natᴴ ]) `× Γ ⇒ᴹ A
  stepᴹ {Γ} {A} h z =
    Cᴹ
      (caseᴹ base succ)
      (Model.distᴹ structure {T = `𝟙} {U = A `× Natᴴ} {V = Γ})
    where
      base : `𝟙 `× Γ ⇒ᴹ A
      base = Cᴹ z π₂ᴹ

      succ : (A `× Natᴴ) `× Γ ⇒ᴹ A
      succ =
        appᴹ
          (appᴹ (Cᴹ h π₂ᴹ)
                 (Cᴹ (π₁ᴹ {T = A} {U = Natᴴ})
                   (π₁ᴹ {T = A `× Natᴴ} {U = Γ})))
          (Cᴹ (π₂ᴹ {T = A} {U = Natᴴ})
            (π₁ᴹ {T = A `× Natᴴ} {U = Γ}))

  precᴹ : ∀ {Γ A : TY HO}
    → Γ ⇒ᴹ A `⇒ Natᴴ `⇒ A
    → Γ ⇒ᴹ A
    → Γ ⇒ᴹ Natᴴ
    → Γ ⇒ᴹ A
  precᴹ h z n = Cᴹ (Pᴹ (stepᴹ h z)) (pairᴹ n idᴹ)

  denote : ∀ {n : Nat.ℕ} {Γ : Ctx n} {A : STy}
    → Exp Γ A
    → ⟦ Γ ⟧ᶜ ⇒ᴹ ⟦ A ⟧ᵀ
  denote (ST.Var i) = lookupᴹ i
  denote (ST.Lam t) = lamᴹ (denote t)
  denote ST.CZero = zeroᴹ
  denote ST.Suc = sucᴹ
  denote (ST.App f x) = appᴹ (denote f) (denote x)
  denote (ST.Nat n) = numeralᴹ n
  denote (ST.PrecT h z n) = precᴹ (denote h) (denote z) (denote n)

  numeral-preserves : ∀ {Γ : TY HO} (n : Nat.ℕ) →
    Model.interpret structure (Ctx⇔PF.compile (numeral {Γ = Γ} n))
      ≈ᴹ numeralᴹ {Γ = Γ} n
  numeral-preserves Nat.zero = ≈-reflᴹ
  numeral-preserves (Nat.suc n) =
    app-congᴹ ≈-reflᴹ (numeral-preserves n)

  lookup-preserves : ∀ {n : Nat.ℕ} {Γ : Ctx n} (i : Fin.Fin n) →
    Model.interpret structure (Ctx⇔PF.compile (lookupᵀ {Γ = Γ} i))
      ≈ᴹ lookupᴹ {Γ = Γ} i
  lookup-preserves {Γ = A ∷ Γ} Fin.zero = ≈-reflᴹ
  lookup-preserves {Γ = A ∷ Γ} (Fin.suc i) =
    C-congᴹ (lookup-preserves {Γ = Γ} i) ≈-reflᴹ

  preserves : ∀ {n : Nat.ℕ} {Γ : Ctx n} {A : STy} (t : Exp Γ A) →
    Model.interpret structure (toPRHO t) ≈ᴹ denote t
  step-preserves : ∀ {n : Nat.ℕ} {Γ : Ctx n} {B : STy}
    (h : Exp Γ (B ST.⇒ (ST.TyNat ST.⇒ B)))
    (z : Exp Γ B) →
    Model.interpret structure
      (Ctx⇔PF.compile (stepᴴ (elab h) (elab z)))
      ≈ᴹ stepᴹ (denote h) (denote z)

  preserves (ST.Var i) = lookup-preserves i
  preserves (ST.Lam t) = lam-congᴹ (preserves t)
  preserves ST.CZero = ≈-reflᴹ
  preserves ST.Suc = ≈-reflᴹ
  preserves (ST.App f x) = app-congᴹ (preserves f) (preserves x)
  preserves (ST.Nat n) = numeral-preserves n
  preserves (ST.PrecT h z n) =
    C-congᴹ
      (P-congᴹ (step-preserves h z))
      (pair-congᴹ (preserves n) ≈-reflᴹ)

  step-preserves h z =
    C-congᴹ
      (case-congᴹ
        (C-congᴹ (preserves z) ≈-reflᴹ)
        (app-congᴹ
          (app-congᴹ
            (C-congᴹ (preserves h) ≈-reflᴹ)
            ≈-reflᴹ)
          ≈-reflᴹ))
      ≈-reflᴹ

----------------------------------------------------------------------
-- Concrete set correctness against the legacy System-T evaluator.
--
-- The executable PR-HO set interpretation represents the Nat inductive
-- object by SetModel.IndSem NatF, with constructor SetModel.nat for the
-- actual numerals.  The logical relation below states that translated
-- System-T terms compute to that concrete encoding of System-T.eval.
----------------------------------------------------------------------

Related : (A : STy) → SetModel.Sem ⟦ A ⟧ᵀ → ST.evalTy A → Set
Related ST.TyNat x n = x ≡ SetModel.nat n
Related (A ST.⇒ B) f g =
  ∀ {x y} → Related A x y → Related B (f x) (g y)

data RelatedCtx : ∀ {n : Nat.ℕ} (Γ : Ctx n)
  → SetModel.Sem ⟦ Γ ⟧ᶜ
  → ST.HVec ST.evalTy Γ
  → Set where
  []ʳ : RelatedCtx [] tt ST.[]ᴴ
  _∷ʳ_ : ∀ {n : Nat.ℕ} {Γ : Ctx n} {A : STy}
    {γ : SetModel.Sem ⟦ Γ ⟧ᶜ}
    {δ : ST.HVec ST.evalTy Γ}
    {a : SetModel.Sem ⟦ A ⟧ᵀ}
    {x : ST.evalTy A}
    → RelatedCtx Γ γ δ
    → Related A a x
    → RelatedCtx (A ∷ Γ) (γ , a) (ST._∷ᴴ_ x δ)

infixr 5 _∷ʳ_

lookup-correct : ∀ {n : Nat.ℕ} {Γ : Ctx n}
  {γ : SetModel.Sem ⟦ Γ ⟧ᶜ}
  {δ : ST.HVec ST.evalTy Γ}
  → (i : Fin.Fin n)
  → RelatedCtx Γ γ δ
  → Related (lookup Γ i)
      (SetModel.interpret (toPRHO (ST.Var i)) γ)
      (ST.hlookup δ i)
lookup-correct {Γ = A ∷ Γ} Fin.zero (relΓ ∷ʳ relA) = relA
lookup-correct {Γ = A ∷ Γ} (Fin.suc i) (relΓ ∷ʳ relA) =
  lookup-correct i relΓ

numeral-correct : ∀ {Γ : TY HO}
  {γ : SetModel.Sem Γ}
  → (n : Nat.ℕ)
  → SetModel.interpret (Ctx⇔PF.compile (numeral {Γ = Γ} n)) γ
      ≡ SetModel.nat n
numeral-correct Nat.zero = refl
numeral-correct {Γ = Γ} {γ = γ} (Nat.suc n)
  rewrite numeral-correct {Γ = Γ} {γ = γ} n = refl

concrete-correct : ∀ {n : Nat.ℕ} {Γ : Ctx n} {A : STy}
  → (t : Exp Γ A)
  → {γ : SetModel.Sem ⟦ Γ ⟧ᶜ}
  → {δ : ST.HVec ST.evalTy Γ}
  → RelatedCtx Γ γ δ
  → Related A (SetModel.interpret (toPRHO t) γ) (ST.eval t δ)
concrete-correct (ST.Var i) relΓ = lookup-correct i relΓ
concrete-correct (ST.Lam t) relΓ relA =
  concrete-correct t (relΓ ∷ʳ relA)
concrete-correct ST.CZero relΓ = refl
concrete-correct ST.Suc relΓ relN rewrite relN = refl
concrete-correct (ST.App f x) relΓ =
  concrete-correct f relΓ (concrete-correct x relΓ)
concrete-correct (ST.Nat n) relΓ = numeral-correct n
concrete-correct {Γ = Γ} (ST.PrecT {ty = A} h z n)
  {γ = γ} {δ = δ} relΓ
  rewrite concrete-correct n relΓ = go (ST.eval n δ)
  where
    step : SetModel.Sem ((NatF [ ⟦ A ⟧ᵀ `× Natᴴ ]) `× ⟦ Γ ⟧ᶜ)
      → SetModel.Sem ⟦ A ⟧ᵀ
    step = SetModel.interpret (Ctx⇔PF.compile (stepᴴ (elab h) (elab z)))

    go : (k : Nat.ℕ)
      → Related A
          (SetModel.paraNat step γ k)
          (ST.para (ST.eval h δ) (ST.eval z δ) k)
    go Nat.zero = concrete-correct z relΓ
    go (Nat.suc k) = concrete-correct h relΓ (go k) refl

closed-nat-correct : ∀ (t : Exp [] ST.TyNat)
  → SetModel.interpret (toPRHO t) tt ≡ SetModel.nat (ST.eval t ST.[]ᴴ)
closed-nat-correct t = concrete-correct t []ʳ
