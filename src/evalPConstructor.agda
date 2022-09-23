{-# OPTIONS --rewriting  #-}
{-# OPTIONS --allow-unsolved-metas #-}

module evalPConstructor where


open import Data.Fin using (Fin; suc; zero; fromℕ; opposite; raise; inject+)
open import Data.Nat using (ℕ; suc; zero; _+_; _≟_; _<″?_; _≤ᵇ_; _∸_)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map)
open import Data.Vec.Properties using (lookup-++ˡ; map-cong; lookup-++ʳ)
open import Function.Base using (id; _∘_; flip)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; _≗_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Equality.Rewrite
open import FinProperties using (inject+0)
open import VecProperties
open import PR-Nat
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Bool hiding (_≟_)

para : ∀ {A : Set} (h : A → ℕ → A) → A → ℕ → A
para h acc zero = acc
para h acc (suc counter) = h (para h acc counter) counter

paraNat : ∀ {n} → (Vec ℕ n → ℕ) → (Vec ℕ (suc (suc n)) → ℕ) → Vec ℕ ( (suc n)) → ℕ
paraNat g h (zero ∷ args) = g args
paraNat g h (suc x ∷ args) = h (paraNat g h (x ∷ args) ∷ (x ∷ args))

paraNat' : ∀ {n} → (Vec ℕ n → ℕ) → (Vec ℕ (suc (suc n)) → ℕ) → Vec ℕ ( (suc n)) → ℕ
paraNat' g h (x ∷ args) = para (λ acc n → h (acc ∷ (n ∷ args))) (g args) x

paraNatPR : ∀ {n : ℕ} (g : PR n) (h : PR (suc (suc n))) (vs : Vec ℕ (suc n) ) → eval (P g h) vs ≡ paraNat (eval g) (eval h) vs
paraNatPR g h (zero ∷ vs) = refl
paraNatPR g h (suc x ∷ vs) rewrite paraNatPR  g h (x ∷ vs)  = refl 



paraNatEq : ∀ {n} → (g : Vec ℕ n → ℕ) → (h : Vec ℕ (suc (suc n)) → ℕ) → (args : Vec ℕ ( (suc n))) → paraNat g h args ≡ paraNat' g h args
paraNatEq g h (zero ∷ args) = refl
paraNatEq g h (suc x ∷ args) rewrite paraNatEq  g h (x ∷ args)  = refl


-- _<b_ : ℕ → ℕ → Bool
-- n <b m = (suc n)  ≤ᵇ  m


-- {-# TERMINATING #-}
-- for : ∀ {A : Set} → A → ℕ → ℕ → (A → ℕ → A) → A
-- for acc i n h  with (n ∸ i)
-- ... | zero = acc
-- ... | suc i = for (h acc i) i n h

-- for2 : ∀ {A : Set} → A → ℕ → ℕ → (A → ℕ → A) → A
-- for2 acc i n h = forHelper acc (n ∸ i) h where
--     forHelper : ∀ {A : Set} → A → ℕ →  (A → ℕ → A) → A
--     forHelper acc zero h = acc
--     forHelper acc (suc n∸i) h = forHelper (h acc i) n∸i h

-- for3 : ∀ {A : Set} → A → ℕ  → (A → ℕ → A) → A
-- for3 acc n∸i h = {!   !}

-- for≡for2 :  ∀ {A : Set} → (acc : A) → (i : ℕ) → (n : ℕ) → (h : A → ℕ → A) → for acc i n h ≡ for2 acc i n h
-- for≡for2 acc zero zero h = refl
-- for≡for2 acc zero (suc n) h = {!   !}
-- for≡for2 acc (suc i) zero h = refl
-- for≡for2 acc (suc i) (suc n) h = {!   !}

-- forEQ : ∀ {A : Set} → (acc : A) → (n : ℕ) → (h : A → ℕ → A)  → for acc 0 (suc n) h ≡ h (for acc 0 (n) h ) n
-- forEQ acc zero h = {!   !}
-- forEQ acc (suc n) h = {!   !}


-- para≡for0 : ∀ {A : Set} → (acc : A) → (n : ℕ) → (h : A → ℕ → A)  → for acc 0 n h ≡ para h acc n
-- para≡for0 acc zero h = refl
-- para≡for0 acc (suc n) h = {!   !}