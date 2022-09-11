
module NatProperties where

open import Data.Nat using (ℕ; suc; zero; _∸_; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; +-comm; +-assoc)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


assoc-comm  :  ∀ (m : ℕ)  (n : ℕ) (o : ℕ) →  (m + (n + o)) ≡   (n + (m + o))
assoc-comm m n o   rewrite  sym ( +-assoc m n o) | sym ( +-assoc  n m o) | +-comm n m = refl


assoc-comm-suc  :  ∀ (m : ℕ)  (n : ℕ) (o : ℕ) →  suc (m + (n + o)) ≡   suc (n + (m + o))
assoc-comm-suc m n o = cong suc (assoc-comm m n o)  