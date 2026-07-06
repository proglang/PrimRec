{-# OPTIONS --safe #-}

module Core.Models.Setoids.PRFOCatamorphism where

open import Level using (Level)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Core.Types
import Core.Models.PRFOCatamorphism as PRFOCatamorphism

----------------------------------------------------------------------
-- Hom-setoid packaging for PR-FO catamorphism-primitive models
----------------------------------------------------------------------

module _ {ℓ : Level} (M : PRFOCatamorphism.Model ℓ) where
  open PRFOCatamorphism.Model M

  homIsEquivalence : ∀ {T U : TY FO} → IsEquivalence (_≈ᴹ_ {T = T} {U = U})
  homIsEquivalence = record
    { refl  = ≈-reflᴹ
    ; sym   = ≈-symᴹ
    ; trans = ≈-transᴹ
    }

  homSetoid : (T U : TY FO) → Setoid ℓ ℓ
  homSetoid T U = record
    { Carrier       = T ⇒ᴹ U
    ; _≈_           = _≈ᴹ_
    ; isEquivalence = homIsEquivalence
    }
