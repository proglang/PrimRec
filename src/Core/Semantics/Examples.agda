{-# OPTIONS --safe #-}

module Core.Semantics.Examples where

open import Data.Empty using (⊥)
open import Data.Fin using (zero)
import Data.Fin as Fin
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Core.Types
open import Core.Semantics.Inductive
open import Core.Semantics.Types

----------------------------------------------------------------------
-- A polynomial first-order natural-number code
----------------------------------------------------------------------

NatF : Ty FO 1
NatF = `𝟙 `+ ` zero

Nat : TY FO
Nat = ind NatF

Nat-guarded : Guarded NatF
Nat-guarded = refl

Nat-wellFormed : WellFormed Nat
Nat-wellFormed = refl

Nat-polynomial : Polynomial Nat
Nat-polynomial = fo-polynomial Nat

zeroN : ⟦ Nat ⟧₀
zeroN = node (inj₁ tt) λ ()

sucN : ⟦ Nat ⟧₀ → ⟦ Nat ⟧₀
sucN n = node (inj₂ tt) λ { refl → n }

fromℕ : ℕ → ⟦ Nat ⟧₀
fromℕ zero    = zeroN
fromℕ (suc n) = sucN (fromℕ n)

-- The inner ind binds zero; suc zero still denotes the recursive variable of
-- the surrounding inductive type.  This is a genuinely nested FO code.
NestedF : Ty FO 1
NestedF = `𝟙 `+ ind (`𝟙 `+ (` zero `× ` (Fin.suc zero)))

Nested : TY FO
Nested = ind NestedF

Nested-wellFormed : WellFormed Nested
Nested-wellFormed = refl

Nested-polynomial : Polynomial Nested
Nested-polynomial = fo-polynomial Nested

----------------------------------------------------------------------
-- A guarded higher-order code with countably many immediate children
----------------------------------------------------------------------

InfTreeF : Ty HO 1
InfTreeF = `𝟙 `+ (lift Nat `⇒ ` zero)

InfTree : TY HO
InfTree = ind InfTreeF

InfTree-guarded : Guarded InfTreeF
InfTree-guarded = refl

InfTree-wellFormed : WellFormed InfTree
InfTree-wellFormed = refl

-- The exponential is precisely what takes this code outside the polynomial
-- PR-FO fragment.
InfTree-not-polynomial : Polynomial InfTreeF → ⊥
InfTree-not-polynomial (poly-+ p ())

leaf∞ : ⟦ InfTree ⟧₀
leaf∞ = node (inj₁ tt) λ ()

-- A node has one recursive child for each semantic natural number.
node∞ : (⟦ Nat ⟧₀ → ⟦ InfTree ⟧₀) → ⟦ InfTree ⟧₀
node∞ children =
  node (inj₂ (λ _ → tt)) λ { (n , refl) → children n }
