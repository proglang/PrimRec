\begin{code}[hide]
module PR-Words where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head)

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Utils

\end{code}
\begin{code}
data PR A : ℕ → Set where
  Z : PR A n
  σ : (a : A) → PR A (suc zero)
  π : (i : Fin n) → PR A n
  C : (f : PR A m) → (g* : Vec (PR A n) m) → PR A n
  P : (g : PR A n) → (h : A → PR A (suc (suc n))) → PR A (suc n)
\end{code}
We superscript the list operations with $^L$ to distinguish them from the vector operations. 
\begin{code}
eval  : PR A n → Vec (List A) n → List A
eval* : Vec (PR A n) m → Vec (List A) n → Vec (List A) m

eval Z        v*               = []ᴸ
eval (σ x)    [ xs ]           = x ∷ᴸ xs
eval (π i)    v*               = lookup v* i
eval (C f g*) v*               = eval f (eval* g* v*)
eval (P g h)  ([]ᴸ ∷ v*)       = eval g v*
eval (P g h)  ((x ∷ᴸ xs) ∷ v*) = eval (h x) (eval (P g h) (xs ∷ v*) ∷ xs ∷ v*)

eval* []       v*              = []
eval* (p ∷ p*) v*              = eval p v* ∷ eval* p* v*
\end{code}
