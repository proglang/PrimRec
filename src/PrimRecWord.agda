module PrimRecWord where

open import Data.Nat using (ℕ; suc; zero; _*_; _+_)
open import Data.Fin using (Fin)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map)
open import Data.List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)

variable
  A : Set                       -- alphabet
  m n : ℕ

module Nats where
  data PRN : ℕ → Set where
    Z : ∀ n → PRN n
    S : PRN (suc zero)
    π : (i : Fin n) → PRN n
    C : PRN m → Vec (PRN n) m → PRN n
    P : (g : PRN n) → (h : PRN (suc (suc n))) → PRN (suc n)

  eval  : PRN n → Vec ℕ n → ℕ
  eval* : Vec (PRN n) m → Vec ℕ n → Vec ℕ m

  eval (Z _) v* = 0
  eval S (x ∷ v*) = suc x
  eval (π i) v* = lookup v* i
  eval (C h g*) v* = eval h (eval* g* v*)
  eval (P g h) (zero ∷ v*) = eval g v*
  eval (P g h) (suc x ∷ v*) = eval h ((eval (P g h) (x ∷ v*)) ∷ (x ∷ v*))

  eval* [] v* = []
  eval* (p ∷ p*) v* = eval p v*  ∷ eval* p* v*

module Words where
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

module Trees where

  Rank : Set → Set
  Rank A = A → ℕ

  data PRR (r : Rank A) : ℕ → Set where
    S : (a : A) → PRR r (r a)
    π : (i : Fin n) → PRR r n
    C : PRR r m → Vec (PRR r n) m → PRR r n
    P : (h : (a : A) → PRR r (r a + r a + n)) → PRR r (suc n)
  
  data Alg (r : Rank A) : Set where
    con : (a : A) → Vec (Alg r) (r a) → Alg r

  {-# TERMINATING #-}
  eval  : ∀ {r : Rank A} → PRR r n → Vec (Alg r) n → Alg r
  eval* : ∀ {r : Rank A} → Vec (PRR r n) m → Vec (Alg r) n → Vec (Alg r) m

  eval (S a) v* = con a v*
  eval (π i) v* = lookup v* i
  eval (C h g*) v* = eval h (eval* g* v*)
  eval {r = r} (P h) (con a xs ∷ v*) = eval (h a) ((map (λ x → eval (P h) (x ∷ v*)) xs ++ xs) ++ v* )

  eval* [] v* = []
  eval* (x ∷ p*) v* = (eval x v*) ∷ (eval* p* v*)

  --- example
  data Alpha : Set where
    Leaf Branch : Alpha

  rankAlpha : Alpha → ℕ
  rankAlpha Leaf = 0
  rankAlpha Branch = 2

  leaf : Alg rankAlpha
  leaf = con Leaf []

  t1 : Alg rankAlpha
  t1 = con Branch (leaf ∷ (leaf ∷ []))

  -- words as trees
  data Letters : Set where
    ε B C : Letters

  rankLetters : Letters → ℕ
  rankLetters ε = 0
  rankLetters B = 1
  rankLetters C = 1

  epsilon : Alg rankLetters
  epsilon = con ε []

  bc : Alg rankLetters
  bc = con B ((con C (epsilon ∷ [])) ∷ [])

  -- numbers as trees
  data Nums : Set where
    Z S : Nums

  rankNums : Rank Nums
  rankNums Z = 0
  rankNums S = 1

  `zero : Alg rankNums
  `zero = con Z []

  `one  : Alg rankNums
  `one  = con S (`zero ∷ [])
