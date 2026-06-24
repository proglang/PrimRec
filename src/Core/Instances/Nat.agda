{-# OPTIONS --safe #-}

module Core.Instances.Nat where

open import Data.Nat using (ℕ)
open import Data.Fin using (zero)
open import Data.Vec using (Vec; []; _∷_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (refl)

import PR-Nat as Source
open import Core.PRFO
open import Core.Instances.Common
open import Core.Semantics.Types using (Guarded; WellFormed; Polynomial)
import Core.Models.PRFO as Model

NatF : Ty FO 1
NatF = `𝟙 `+ ` zero

Nat : TY FO
Nat = ind NatF

NatF-guarded : Guarded NatF
NatF-guarded = refl

NatF-wellFormed : WellFormed NatF
NatF-wellFormed = refl

NatF-polynomial : Polynomial NatF
NatF-polynomial = Core.Semantics.Types.fo-polynomial NatF

Nat-wellFormed : WellFormed Nat
Nat-wellFormed = refl

Nat-polynomial : Polynomial Nat
Nat-polynomial = Core.Semantics.Types.fo-polynomial Nat

compile : ∀ {n} → Source.PR n → vec Nat n →ᴾ Nat
compile* : ∀ {m n} → Vec (Source.PR n) m → vec Nat n →ᴾ vec Nat m

compile Source.Z = C fold ι₁
compile Source.σ = C (C fold ι₂) π₁
compile (Source.π i) = lookupᴾ i
compile (Source.C f fs) = C (compile f) (compile* fs)
compile (Source.P g h) =
  P (C (`case (C (compile g) π₂)
              (C (compile h) assoc-×))
       dist-+-×)
compile (Source.F g h) =
  P (C (`case (C (compile g) π₂)
              (C (compile h) (`# (C π₁ π₁) π₂)))
       dist-+-×)

compile* []       = `⊤
compile* (p ∷ ps) = `# (compile p) (compile* ps)

-- Typing is intrinsic in the result of compile.  PR-NAT has no type
-- variables, so there is no type-substitution obligation at this source
-- level.
compile-typed : ∀ {n} → Source.PR n → Set
compile-typed {n} p = vec Nat n →ᴾ Nat

typed : ∀ {n} (p : Source.PR n) → compile-typed p
typed = compile

----------------------------------------------------------------------
-- Categorical source semantics and preservation
----------------------------------------------------------------------

module Semantics {ℓ : Level} (M : Model.Model ℓ) where
  open Model.Model M

  assocᴹ : ∀ {T U V} → (T `× U) `× V ⇒ᴹ T `× (U `× V)
  assocᴹ = pairᴹ (Cᴹ π₁ᴹ π₁ᴹ) (pairᴹ (Cᴹ π₂ᴹ π₁ᴹ) π₂ᴹ)

  denote : ∀ {n} → Source.PR n → vec Nat n ⇒ᴹ Nat
  denote* : ∀ {m n} → Vec (Source.PR n) m → vec Nat n ⇒ᴹ vec Nat m

  denote Source.Z = Cᴹ foldᴹ ι₁ᴹ
  denote Source.σ = Cᴹ (Cᴹ foldᴹ ι₂ᴹ) π₁ᴹ
  denote (Source.π i) = Model.interpret structure (lookupᴾ i)
  denote (Source.C f fs) = Cᴹ (denote f) (denote* fs)
  denote (Source.P g h) =
    Pᴹ (Cᴹ (caseᴹ (Cᴹ (denote g) π₂ᴹ)
                       (Cᴹ (denote h) assocᴹ))
          distᴹ)
  denote (Source.F g h) =
    Pᴹ (Cᴹ (caseᴹ (Cᴹ (denote g) π₂ᴹ)
                       (Cᴹ (denote h) (pairᴹ (Cᴹ π₁ᴹ π₁ᴹ) π₂ᴹ)))
          distᴹ)

  denote* []       = ⊤ᴹ
  denote* (p ∷ ps) = pairᴹ (denote p) (denote* ps)

  preserves : ∀ {n} (p : Source.PR n) →
              Model.interpret structure (compile p) ≈ᴹ denote p
  preserves* : ∀ {m n} (ps : Vec (Source.PR n) m) →
               Model.interpret structure (compile* ps) ≈ᴹ denote* ps

  preserves Source.Z = ≈-reflᴹ
  preserves Source.σ = ≈-reflᴹ
  preserves (Source.π i) = ≈-reflᴹ
  preserves (Source.C f fs) = C-congᴹ (preserves f) (preserves* fs)
  preserves (Source.P g h) =
    P-congᴹ
      (C-congᴹ
        (case-congᴹ (C-congᴹ (preserves g) ≈-reflᴹ)
          (C-congᴹ (preserves h) ≈-reflᴹ))
        ≈-reflᴹ)
  preserves (Source.F g h) =
    P-congᴹ
      (C-congᴹ
        (case-congᴹ (C-congᴹ (preserves g) ≈-reflᴹ)
          (C-congᴹ (preserves h) ≈-reflᴹ))
        ≈-reflᴹ)

  preserves* [] = ≈-reflᴹ
  preserves* (p ∷ ps) = pair-congᴹ (preserves p) (preserves* ps)

  infix 4 _≈Source_
  _≈Source_ : ∀ {n} → Source.PR n → Source.PR n → Set ℓ
  p ≈Source q = denote p ≈ᴹ denote q

  equations-preserved : ∀ {n} {p q : Source.PR n} →
    p ≈Source q →
    Model.interpret structure (compile p) ≈ᴹ Model.interpret structure (compile q)
  equations-preserved {p = p} {q = q} equation =
    ≈-transᴹ (preserves p) (≈-transᴹ equation (≈-symᴹ (preserves q)))
