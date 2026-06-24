{-# OPTIONS --safe #-}

module Core.Semantics.Containers where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

----------------------------------------------------------------------
-- Indexed containers
----------------------------------------------------------------------

-- A container with n kinds of holes.  Its extension at an environment ρ
-- consists of a shape together with a value for every hole in that shape.
record Container (n : ℕ) : Set₁ where
  field
    Shape    : Set
    Position : Shape → Fin n → Set

open Container public

Value : ∀ {n} → Container n → (Fin n → Set) → Set
Value C ρ = Σ (Shape C) λ s → ∀ i → Position C s i → ρ i

mapC : ∀ {n} {C : Container n} {ρ σ : Fin n → Set} →
       (∀ i → ρ i → σ i) → Value C ρ → Value C σ
mapC f (s , values) = s , λ i p → f i (values i p)

strengthC : ∀ {n} {C : Container n} {ρ : Fin n → Set} {A : Set} →
            Value C ρ × A → Value C (λ i → ρ i × A)
strengthC ((s , values) , a) = s , λ i p → values i p , a

zeroC : ∀ {n} → Container n
zeroC = record
  { Shape    = ⊥
  ; Position = λ ()
  }

oneC : ∀ {n} → Container n
oneC = record
  { Shape    = ⊤
  ; Position = λ _ _ → ⊥
  }

varC : ∀ {n} → Fin n → Container n
varC i = record
  { Shape    = ⊤
  ; Position = λ _ j → i ≡ j
  }

infixr 7 _×C_
infixr 8 _+C_

_+C_ : ∀ {n} → Container n → Container n → Container n
C +C D = record
  { Shape = Shape C ⊎ Shape D
  ; Position = λ
      { (inj₁ s) i → Position C s i
      ; (inj₂ t) i → Position D t i
      }
  }

_×C_ : ∀ {n} → Container n → Container n → Container n
C ×C D = record
  { Shape    = Shape C × Shape D
  ; Position = λ { (s , t) i → Position C s i ⊎ Position D t i }
  }

Closed : Container 0 → Set
Closed C = Shape C

-- Positive exponentials are still containers.  A shape chooses one codomain
-- shape for every closed argument; a hole records the argument at which the
-- corresponding codomain hole occurs.
expC : Container 0 → ∀ {n} → Container n → Container n
expC A B = record
  { Shape    = Closed A → Shape B
  ; Position = λ f i → Σ (Closed A) λ a → Position B (f a) i
  }
