{-# OPTIONS --safe #-}

module Core.Instances.SystemT where

import Data.Fin as Fin
import Data.Nat as Nat
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import System-T as ST
open import Core.Types
import Core.Contextual.PRHO as Ctx
import Core.Contextual.Equations.PRHO as CtxEq
import Core.PRHO as PF
import Core.Equations.PRHO as PFEq
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
zeroᴴ = Ctx.cut Ctx.fold (Ctx.cut Ctx.inl Ctx.unit)

sucᴴ : ∀ {Γ : TY HO} → Γ Ctx.⊢ Natᴴ `⇒ Natᴴ
sucᴴ = Ctx.curry (Ctx.cut Ctx.fold (Ctx.cut Ctx.inr Ctx.snd))

numeral : ∀ {Γ : TY HO} → Nat.ℕ → Γ Ctx.⊢ Natᴴ
numeral Nat.zero = zeroᴴ
numeral (Nat.suc n) = app sucᴴ (numeral n)

stepᴴ : ∀ {Γ A : TY HO}
  → Γ Ctx.⊢ A `⇒ Natᴴ `⇒ A
  → Γ Ctx.⊢ A
  → (NatF ⇐ (A `× Natᴴ)) `× Γ Ctx.⊢ A
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
