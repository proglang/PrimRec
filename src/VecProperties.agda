{-# OPTIONS --rewriting  #-}

module VecProperties where

open import Data.Fin using (Fin; suc; zero; fromℕ; opposite; raise; inject+; inject₁; toℕ)
open import Data.Nat using (ℕ; suc; zero; _∸_; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; +-comm; +-assoc)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head; init; last; foldl) -- ; _ʳ++_) 
open import Function.Base using (const; _∘′_; id; _∘_)
open import Data.Fin.Properties using (toℕ-fromℕ; fromℕ-toℕ) -- (++-assoc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Equality.Rewrite
open import NatProperties using (assoc-comm-suc)
open import FinProperties using (inject+0; inject+1; inject+Add; inject+Eq)

open import Utils



_++r_ : ∀ {A : Set}{m n} → Vec A m → Vec A n → Vec A (m + n)
(x ∷ xs)      ++r ys = xs ++r (x ∷ ys)
[] ++r ys =  ys

fastReverse : ∀ {A : Set} {m : ℕ} → Vec A m → Vec A m
fastReverse vs = vs ++r []


 
{-# REWRITE inject+Eq #-}


lkupfromN'' : ∀  {A}{m n o :  ℕ}(xs : Vec A m) (ys : Vec A ((suc n) + (o))) → lookup ((xs ++r ys))   (inject+ {suc(m + n)} o (fromℕ ( m + n)))   ≡  lookup ys ( (inject+ o (fromℕ (n ))))
lkupfromN'' [] (x ∷ ys) = refl
lkupfromN'' {A} {suc m} {n} {o} (x ∷ xs) (y ∷ ys) = lkupfromN'' {A} {m} {suc n} {o} xs (x ∷ (y ∷ ys))

lkupfromN' : ∀  {A} {n m v}(vs : Vec A (n)) (ys : Vec A (m))   → lookup (vs ++r (v ∷ ys)) (inject+ m (fromℕ n)) ≡ v
lkupfromN' {A} {n} {m} {v} (xs) (ys) = lkupfromN'' {A} {n} xs (v ∷ ys ) 


lookupOP' : ∀  {A} {n m : ℕ} (f : Fin ((n)) ) (vs : Vec A (n)) (ys : Vec A (m))  → lookup (vs ++r ys) (inject+ m (opposite f)) ≡ lookup vs f
lookupOP' zero (v ∷ vs) ys = lkupfromN' vs ys
lookupOP' (suc f) (x ∷ vs) (ys) = lookupOP' f (vs) ((x ∷ ys))

lookupOpRev :  ∀ {A : Set} {n} (f : Fin n) (xs : Vec A n) → lookup (fastReverse xs) (opposite f)  ≡ lookup  (xs) f
lookupOpRev f xs rewrite sym(inject+0 (opposite f)) = lookupOP' f xs []





-- lookupRaise : ∀ {A : Set} {n m} (f : Fin n) (xs : Vec A n) (ys : Vec A m) → lookup xs f ≡ lookup (xs ++ ys) (inject+ m f) 
-- lookupRaise f xs [] = {!   !}
-- lookupRaise f xs (x ∷ ys) = {!   !}


assoc++ : ∀ {A : Set} {n m o : ℕ} → (xs : Vec A n) (ys : Vec A m)(zs : Vec A o) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc++ [] ys zs = refl
assoc++ {A} {suc n} {m} {o} (x ∷ xs) ys zs = cong (λ v → x ∷ v) (assoc++ {A}{n} {m} {o} xs ys zs)

-- helperRev : ∀ {A : Set} {n : ℕ} (x : A) (xs : Vec A n) → fastReverse (x ∷ xs) ≡ (fastReverse xs) ++ (x ∷ [])
-- helperRev x [] = refl
-- helperRev x (y ∷ xs) = {!   !}

-- see TAPL lists

reverse  : ∀ {A : Set} {n : ℕ} → ( Vec A n) → ( Vec A n)
reverse [] = []
reverse (x ∷ vs) = (reverse vs) ++ [ x ]

++r-reverse' : ∀ {A : Set} {m n : ℕ}  (xs : Vec A m) (ys : Vec A n) →    (xs ++r ys) ≡ ((reverse xs) ++ ys)
++r-reverse' [] (ys) = refl
++r-reverse'  (x ∷ xs) ys rewrite ++r-reverse' xs (x ∷ ys) = 
    (reverse xs) ++ x ∷ ys 
        ≡⟨⟩ 
    (reverse xs) ++ ( [ x ] ++ ys) 
        ≡⟨ (assoc++ (reverse xs) [ x ] ys) ⟩ 
    ((reverse xs ++ [ x ]) ++ ys) 
        ≡⟨⟩
    reverse ( x ∷ xs) ++ ys ∎