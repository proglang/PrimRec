module PR-Nat-Example where

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_; _*_; _∸_)
-- open import Data.Nat.Properties using (+-identityʳ; +-suc; +-∸-assoc; ∸-+-assoc)
open import Data.Vec using (Vec; []; _∷_; _++_)

open import Utils

open import PR-Nat

addP : PR 2
addP = P (π zero) (C σ [ π zero ])

addP=+ : ∀ m n → eval addP [ m , n ] ≡ m + n
addP=+ zero n = refl
addP=+ (suc m) n = cong suc (addP=+ m n)

mulP : PR 2
mulP = P Z (C addP [ π (suc (suc zero)) , π zero ])

mulP=* : ∀ m n → eval mulP [ m , n ] ≡ m * n
mulP=* zero n = refl
mulP=* (suc m) n
  rewrite mulP=* m n
        | addP=+ n (m * n) = refl

predP : PR 1
predP = P Z (π (suc zero))

predP=∸1 : ∀ m → eval predP [ m ] ≡ m ∸ 1
predP=∸1 zero = refl
predP=∸1 (suc m) = refl

subP : PR 2
subP = C (P (π zero) (C predP [ π zero ])) [ π (suc zero) , π zero ]

m∸n∸1≡m∸sucn : ∀ m n → m ∸ n ∸ 1 ≡ m ∸ suc n
m∸n∸1≡m∸sucn zero zero = refl
m∸n∸1≡m∸sucn zero (suc n) = refl
m∸n∸1≡m∸sucn (suc m) zero = refl
m∸n∸1≡m∸sucn (suc m) (suc n) = m∸n∸1≡m∸sucn m n

subP=∸ : ∀ m n → eval subP [ m , n ] ≡ m ∸ n
subP=∸ m zero = refl
subP=∸ m (suc n)
  rewrite subP=∸ m n
        | predP=∸1 (m ∸ n) = m∸n∸1≡m∸sucn m n

