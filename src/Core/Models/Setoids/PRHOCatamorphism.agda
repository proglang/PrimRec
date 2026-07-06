{-# OPTIONS --safe #-}

module Core.Models.Setoids.PRHOCatamorphism where

open import Level using (Level)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Core.Types
import Core.Models.PRHOCatamorphism as PRHOCatamorphism

----------------------------------------------------------------------
-- Hom-setoid packaging for PR-HO catamorphism-primitive models
----------------------------------------------------------------------

module _ {ℓ : Level} (M : PRHOCatamorphism.Model ℓ) where
  open PRHOCatamorphism.Model M

  homIsEquivalence : ∀ {T U : TY HO} → IsEquivalence (_≈ᴹ_ {T = T} {U = U})
  homIsEquivalence = record
    { refl  = ≈-reflᴹ
    ; sym   = ≈-symᴹ
    ; trans = ≈-transᴹ
    }

  homSetoid : (T U : TY HO) → Setoid ℓ ℓ
  homSetoid T U = record
    { Carrier       = T ⇒ᴹ U
    ; _≈_           = _≈ᴹ_
    ; isEquivalence = homIsEquivalence
    }
