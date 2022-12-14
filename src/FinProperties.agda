{-# OPTIONS --rewriting #-}
module FinProperties where

open import Data.Fin using (Fin; suc; zero; fromℕ; opposite; raise; inject+; inject₁)
open import Data.Nat using (ℕ; suc; zero; _∸_; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; +-comm; +-assoc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Equality.Rewrite

{-# REWRITE +-identityʳ +-suc +-assoc #-}



inject+0 :  ∀ {m}  (f  : Fin m)  → inject+ zero f ≡ f
inject+0 zero = refl
inject+0 (suc f) = cong suc (inject+0 f)

inject+1 : ∀ {m}  (f  : Fin m)  → inject+ 1 ( f) ≡ inject₁ ( f) 
inject+1 {suc zero} zero = refl
inject+1 {suc (suc m)} zero = refl 
inject+1 {suc (suc m)} (suc f) = cong suc (inject+1 f)



inject+Add : ∀ (m :  ℕ )( n : ℕ){o : ℕ} (f : Fin o) → (inject+ {o} (m + n) f) ≡ (inject+ {o + m}  n    (inject+ m f))
inject+Add m n {suc o} zero = refl
inject+Add ( m) ( n) {suc o} (suc f) = cong suc (inject+Add ( m) ( n) {o} f)

inject+Eq : ∀ {m}(n)  (f  : Fin m)  →  (inject+ ( n) (inject₁ ( f))) ≡ (inject+ ( (suc n)) ( f))
inject+Eq m f rewrite sym (inject+1 f) = sym (inject+Add 1 m f)


raiseAdd : ∀ (m :  ℕ )( n : ℕ){o : ℕ} (f : Fin o) → (raise {o} (m + n) f) ≡ (raise {n + o}  m    (raise n f))
raiseAdd zero n {o} f = refl
raiseAdd (suc m) n {o} f = cong suc (raiseAdd ( m) ( n) {o} f)


raiseSuc : ∀ ( n m : ℕ) (f) → raise n (suc {m} (f)) ≡ suc (raise n (f)) 
raiseSuc n m f = sym (raiseAdd n 1 f)