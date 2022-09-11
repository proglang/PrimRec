{-# OPTIONS --rewriting --prop -v rewriting:50 #-}
module FinProperties where

open import Data.Fin using (Fin; suc; zero; fromℕ; opposite; raise; inject+; inject₁; toℕ)
open import Data.Nat using (ℕ; suc; zero; _∸_; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; +-comm; +-assoc)
open import Data.Fin.Properties using (toℕ-fromℕ; fromℕ-toℕ) -- (++-assoc)
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

-- {-# REWRITE Inject+0  #-}


inject+Add : ∀ (m :  ℕ )( n : ℕ){o : ℕ} (f : Fin o) → (inject+ {o} (m + n) f) ≡ (inject+ {o + m}  n    (inject+ m f))
inject+Add m n {suc o} zero = refl
inject+Add ( m) ( n) {suc o} (suc f) = cong suc (inject+Add ( m) ( n) {o} f)

inject+Eq : ∀ {m}(n)  (f  : Fin m)  →  (inject+ ( n) (inject₁ ( f))) ≡ (inject+ ( (suc n)) ( f))
inject+Eq m f rewrite sym (inject+1 f) = sym (inject+Add 1 m f)