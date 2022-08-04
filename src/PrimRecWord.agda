module PrimRecWord where

open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec; []; _∷_; lookup; map)
open import Data.List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

variable
  A : Set
  m n : ℕ

data PRW (A : Set) : ℕ → Set where
  Z : ∀ n → PRW A n
  S : (a : A) → PRW A (suc zero)
  π : (i : Fin n) → PRW A n
  C : PRW A m → Vec (PRW A n) m → PRW A n
  P : (g : PRW A n) → (h : A → PRW A (suc (suc n))) → PRW A (suc n)

eval  : PRW A n → Vec (List A) n → List A
eval* : Vec (PRW A n) m → Vec (List A) n → Vec (List A) m

eval (Z n)    v*               = []ᴸ
eval (S x)    (xs ∷ v*)        = x ∷ᴸ xs
eval (π i)    v*               = lookup v* i
eval (C h g*) v*               = eval h (eval* g* v*)
eval (P g h)  ([]ᴸ ∷ v*)       = eval g v*
eval (P g h)  ((x ∷ᴸ xs) ∷ v*) = eval (h x) (eval (P g h) (xs ∷ v*) ∷ xs ∷ v*)

eval* [] v* = []
eval* (p ∷ p*) v* = eval p v* ∷ eval* p* v*
