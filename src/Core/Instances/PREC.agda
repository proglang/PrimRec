{-# OPTIONS --safe #-}

module Core.Instances.PREC where

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; map)
open import Relation.Binary.PropositionalEquality using (_≡_)

import PR-Nat as Source
open import Core.PRFO using (FO; TY; _→ᴾ_; C; id)
import Core.Equations.PRFO as CoreEq
open import Core.Instances.Common using (vec)
open import Core.Instances.Nat using (Nat; compile*)

----------------------------------------------------------------------
-- The category PREC of vector-valued primitive recursive maps
----------------------------------------------------------------------

Obj : Set
Obj = ℕ

Hom : Obj → Obj → Set
Hom n m = Vec (Source.PR n) m

idᵖʳ : ∀ {n} → Hom n n
idᵖʳ {n} = map Source.π (Source.allFin n)

infixr 9 _∘ᵖʳ_
_∘ᵖʳ_ : ∀ {n m k} → Hom m k → Hom n m → Hom n k
fs ∘ᵖʳ gs = map (λ f → Source.C f gs) fs

infix 4 _≈ᵖʳ_
_≈ᵖʳ_ : ∀ {n m} → Hom n m → Hom n m → Set
fs ≈ᵖʳ gs = ∀ xs → Source.eval* fs xs ≡ Source.eval* gs xs

----------------------------------------------------------------------
-- Finite-Nat subcategory of the PR-FO target
----------------------------------------------------------------------

NatObj : Obj → TY FO
NatObj n = vec Nat n

NatHom : Obj → Obj → Set
NatHom n m = NatObj n →ᴾ NatObj m

idᴺ : ∀ {n} → NatHom n n
idᴺ = id

infixr 9 _∘ᴺ_
_∘ᴺ_ : ∀ {n m k} → NatHom m k → NatHom n m → NatHom n k
f ∘ᴺ g = C f g

infix 4 _≈ᴺ_
_≈ᴺ_ : ∀ {n m} → NatHom n m → NatHom n m → Set
_≈ᴺ_ = CoreEq._≈_

----------------------------------------------------------------------
-- Object and arrow map induced by the Nat instance compiler
----------------------------------------------------------------------

F₀ : Obj → TY FO
F₀ = NatObj

F₁ : ∀ {n m} → Hom n m → NatHom n m
F₁ = compile*
