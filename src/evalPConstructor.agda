{-# OPTIONS --rewriting  #-}
{-# OPTIONS --allow-unsolved-metas #-}

module evalPConstructor where


open import Data.Fin using (Fin; suc; zero; fromℕ; opposite; raise; inject+)
open import Data.Nat using (ℕ; suc; zero; _+_; _≟_; _<″?_; _≤ᵇ_)
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

-- for : ∀ {A : Set} → A → ℕ → ℕ → (A → ℕ → A) → A
-- for acc i n h  with n - i
-- ... | (suc n) = for (h acc i)(i + 1) n h
-- ... | zero = acc