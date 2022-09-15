\begin{code}
module PR-Trees-Examples where

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; suc; zero; _*_; _+_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head)
open import Data.Vec.Properties using (lookup-map)
open import Data.List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_; _++_ to _++ᴸ_; length to lengthᴸ; map to mapᴸ)
open import Function using (_∘_)

open import Utils

open import PR-Trees

--- example
data Alpha : Set where
  Leaf Branch : Alpha

rankAlpha : Alpha → ℕ
rankAlpha Leaf = 0
rankAlpha Branch = 2

RAlpha = mkRanked Alpha rankAlpha

leaf : Term RAlpha
leaf = con Leaf []

t1 : Term RAlpha
t1 = con Branch (leaf ∷ (leaf ∷ []))


-- words as trees
data Letters : Set where
  ε B C : Letters

rankLetters : Letters → ℕ
rankLetters ε = 0
rankLetters B = 1
rankLetters C = 1

RLetters = mkRanked Letters rankLetters

epsilon : Term RLetters
epsilon = con ε []

bc : Term RLetters
bc = con B ((con C (epsilon ∷ [])) ∷ [])

-- numbers as trees
data Nums : Set where
  `Z `S : Nums

rankNums : Nums → ℕ
rankNums `Z = 0
rankNums `S = 1

RNums = mkRanked Nums rankNums

`zero : Term RNums
`zero = con `Z []

`one  : Term RNums
`one  = con `S (`zero ∷ [])

\end{code}

