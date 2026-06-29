{-# OPTIONS --safe #-}

module Core.Models.Setoids.PRFO where

open import Level using (Level)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Core.Types
import Core.Models.PRFO as PRFO

----------------------------------------------------------------------
-- Hom-setoid packaging for PR-FO models
----------------------------------------------------------------------

module _ {ℓ : Level} (M : PRFO.Model ℓ) where
  open PRFO.Model M

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
