{-# OPTIONS --safe #-}

module Core.Models.Setoids.PRFOFold where

open import Level using (Level)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Core.Types
import Core.Models.PRFOFold as PRFOFold

----------------------------------------------------------------------
-- Hom-setoid packaging for PR-FO fold-primitive models
----------------------------------------------------------------------

module _ {ℓ : Level} (M : PRFOFold.Model ℓ) where
  open PRFOFold.Model M

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
