{-# OPTIONS --safe #-}

module Core.Instances.Source.Trees where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; tabulate)

record Ranked : Set where
  constructor ranked
  field
    {count} : ℕ
    ranks   : Vec ℕ count

open Ranked public

rank : (R : Ranked) → Fin (count R) → ℕ
rank R = lookup (ranks R)

data PR (R : Ranked) : ℕ → Set where
  σ : (a : Fin (count R)) → PR R (rank R a)
  π : ∀ {n} → Fin n → PR R n
  C : ∀ {m n} → PR R m → Vec (PR R n) m → PR R n
  P : ∀ {n} →
      ((a : Fin (count R)) → PR R ((rank R a + rank R a) + n)) →
      PR R (suc n)

data Term (R : Ranked) : Set where
  con : (a : Fin (count R)) → (Fin (rank R a) → Term R) → Term R

para : ∀ {R} {A : Set} →
       ((a : Fin (count R)) → (Fin (rank R a) → A × Term R) → A) →
       Term R → A
para algebra (con a children) =
  algebra a (λ i → para algebra (children i) , children i)

eval : ∀ {R n} → PR R n → Vec (Term R) n → Term R
eval* : ∀ {R m n} → Vec (PR R n) m → Vec (Term R) n → Vec (Term R) m

eval (σ a) values = con a (lookup values)
eval (π i) values = lookup values i
eval (C f fs) values = eval f (eval* fs values)
eval {R} {suc n} (P steps) (tree ∷ parameters) =
  para algebra tree
  where
  algebra : (a : Fin (count R)) →
    (Fin (rank R a) → Term R × Term R) → Term R
  algebra a children =
    eval (steps a)
      ((map proj₁ (tabulate children) ++ map proj₂ (tabulate children)) ++ parameters)

eval* [] values = []
eval* (p ∷ ps) values = eval p values ∷ eval* ps values
