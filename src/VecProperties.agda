{-# OPTIONS --rewriting --prop -v rewriting:50 #-}

module VecProperties where

open import Data.Fin using (Fin; suc; zero; fromℕ; opposite; raise; inject+; inject₁; toℕ)
open import Data.Nat using (ℕ; suc; zero; _∸_; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; +-comm; +-assoc)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head; init; reverse; last; foldl) -- ; _ʳ++_) 
open import Function.Base using (const; _∘′_; id; _∘_)
open import Data.Fin.Properties using (toℕ-fromℕ; fromℕ-toℕ) -- (++-assoc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Equality.Rewrite
open import NatProperties using (assoc-comm-suc)
open import FinProperties using (inject+0; inject+1; inject+Add; inject+Eq)



_++r_ : ∀ {A : Set}{m n} → Vec A m → Vec A n → Vec A (m + n)
(x ∷ xs)      ++r ys = xs ++r (x ∷ ys)
[] ++r ys =  ys



++r-reverse' : ∀ {A : Set} {m n : ℕ}  (xs : Vec A m) (ys : Vec A n) →    (xs ++r ys) ≡ ((reverse xs) ++ ys)
++r-reverse' {A} {zero} {n} [] ys = refl 
++r-reverse' (x ∷ xs) ys rewrite ++r-reverse' xs ((x ∷ ys)) = {!   !}

++r-reverse : ∀ {A : Set}{m} (xs : Vec A m) → xs ++r [] ≡ (reverse xs)
++r-reverse [] = refl
++r-reverse (x ∷ xs) = {!   !}


lookupOpRev :  ∀ {A : Set} {n} (f : Fin n) (xs : Vec A n) → lookup (reverse xs) (opposite f)  ≡ lookup  (xs) f
lookupOpRev zero (x ∷ []) = {!   !}
lookupOpRev zero (x ∷ y ∷ xs) = {!   !} 
lookupOpRev {A} {suc (suc n)} (suc f) (x ∷ y ∷ xs)  = {!    !} 



lookupOP : ∀  {n : ℕ} (f : Fin ((suc n)) ) (vs : Vec ℕ (suc n))  → lookup (vs ++r []) (opposite f) ≡ lookup vs f
lookupOP {.zero} zero (x ∷ []) = refl
lookupOP zero (x ∷ x₁ ∷ vs) = {!   !}
lookupOP {n} (suc f) (x ∷ vs) = {!n   !}

lookupInj : ∀  {n x : ℕ} (f : Fin ((n)) )(vs : Vec ℕ (n))  → lookup  vs f  ≡ lookup(x ∷ vs)  (inject₁ f) 
lookupInj zero (x ∷ vs) = {!   !}
lookupInj (suc f) (x ∷ vs) = {!   !}
 
{-# REWRITE inject+Eq #-}


lookupOP' : ∀  {n m : ℕ} (f : Fin ((n)) ) (vs : Vec ℕ (n)) (ys : Vec ℕ (m))  → lookup (vs ++r ys) (inject+ m (opposite f)) ≡ lookup vs f
lookupOP' zero (v ∷ vs) ys = {!  !}
lookupOP' (suc f) (x ∷ vs) (ys) = lookupOP' f (vs) ((x ∷ ys)) --  


lkupfromN' : ∀  {n m v}(vs : Vec ℕ (n)) (ys : Vec ℕ (m))   → lookup (vs ++r (v ∷ ys)) (inject+ m (fromℕ n)) ≡ v
lkupfromN' {n} {m} {v} (xs) (ys) = {!   ys!} 

lkupfromN :  ∀  {n}(vs : Vec ℕ (suc n)) → lookup (vs)  ((fromℕ n)) ≡   last vs
lkupfromN (x ∷ []) = refl
lkupfromN {suc (n)} (x ∷ x₁ ∷ vs) = sym (last (x ∷ x₁ ∷ vs) ≡⟨⟩ {! last (x₁ ∷ vs)  !} ≡⟨⟩ ({!   !} ≡⟨⟩ {!   !}) )


{-# REWRITE assoc-comm-suc #-}

--  (inject+ o (fromℕ (n + m))) -- (xs ++r ys)
lkupfromN'' : ∀  {m n o :  ℕ}(xs : Vec ℕ m) (ys : Vec ℕ ((suc n) + (o))) → lookup ((xs ++r ys))   (inject+ {suc(m + n)} o (fromℕ ( m + n)))   ≡  lookup ys ( (inject+ o (fromℕ (n ))))
lkupfromN'' [] (x ∷ ys) = refl
lkupfromN'' {suc m} {n} {o} (x ∷ xs) (y ∷ ys) = lkupfromN'' {m} {suc n} {o} xs (x ∷ (y ∷ ys))