{-# OPTIONS --safe #-}

module Core.Instances.Trees where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Level using (Level)

open import Core.PRFO
open import Core.Instances.Common
import Core.Instances.Model as InstanceModel
import Core.Instances.Source.Trees as Source
import Core.Models.PRFO as Model

Target : Source.Ranked → TY FO
Target R = Tree (Source.ranks R)

compile : ∀ {R n} → Source.PR R n → vec (Target R) n →ᴾ Target R
compile* : ∀ {R m n} → Vec (Source.PR R n) m →
           vec (Target R) n →ᴾ vec (Target R) m

compile {R} (Source.σ a) = conᴾ (Source.ranks R) a
compile (Source.π i) = lookupᴾ i
compile (Source.C f fs) = C (compile f) (compile* fs)
compile {R} {n = _} (Source.P steps) =
  P (paraHandler (Source.ranks R) (λ i → compile (steps i)))

compile* []       = `⊤
compile* (p ∷ ps) = `# (compile p) (compile* ps)

compile-typed : ∀ {R n} → Source.PR R n → Set
compile-typed {R} {n} p = vec (Target R) n →ᴾ Target R

typed : ∀ {R n} (p : Source.PR R n) → compile-typed p
typed = compile

-- Source arities contain no type variables, hence there is no separate
-- type-substitution compatibility statement for this compiler.

----------------------------------------------------------------------
-- Categorical source semantics and preservation
----------------------------------------------------------------------

module Semantics {ℓ : Level} (M : Model.Model ℓ) where
  open Model.Model M
  open InstanceModel.For M

  denote : ∀ {R n} → Source.PR R n → vec (Target R) n ⇒ᴹ Target R
  denote* : ∀ {R m n} → Vec (Source.PR R n) m →
            vec (Target R) n ⇒ᴹ vec (Target R) m

  denote {R} (Source.σ a) = Model.interpret structure (conᴾ (Source.ranks R) a)
  denote (Source.π i) = Model.interpret structure (lookupᴾ i)
  denote (Source.C f fs) = Cᴹ (denote f) (denote* fs)
  denote {R} {suc n} (Source.P steps) =
    Pᴹ (paraHandlerᴹ (Source.ranks R) (λ i → denote (steps i)))

  denote* []       = ⊤ᴹ
  denote* (p ∷ ps) = pairᴹ (denote p) (denote* ps)

  preserves : ∀ {R n} (p : Source.PR R n) →
              Model.interpret structure (compile p) ≈ᴹ denote p
  preserves* : ∀ {R m n} (ps : Vec (Source.PR R n) m) →
               Model.interpret structure (compile* ps) ≈ᴹ denote* ps

  preserves (Source.σ a) = ≈-reflᴹ
  preserves (Source.π i) = ≈-reflᴹ
  preserves (Source.C f fs) = C-congᴹ (preserves f) (preserves* fs)
  preserves {R} {suc n} (Source.P steps) =
    P-congᴹ
      (≈-transᴹ
        (paraHandler-interpret (Source.ranks R) (λ i → compile (steps i)))
        (paraHandler-congᴹ (Source.ranks R) (λ i → preserves (steps i))))

  preserves* [] = ≈-reflᴹ
  preserves* (p ∷ ps) = pair-congᴹ (preserves p) (preserves* ps)

  infix 4 _≈Source_
  _≈Source_ : ∀ {R n} → Source.PR R n → Source.PR R n → Set ℓ
  p ≈Source q = denote p ≈ᴹ denote q

  equations-preserved : ∀ {R n} {p q : Source.PR R n} →
    p ≈Source q →
    Model.interpret structure (compile p) ≈ᴹ Model.interpret structure (compile q)
  equations-preserved {p = p} {q = q} equation =
    ≈-transᴹ (preserves p) (≈-transᴹ equation (≈-symᴹ (preserves q)))
