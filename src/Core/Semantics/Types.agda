{-# OPTIONS --safe #-}

module Core.Semantics.Types where

open import Data.Bool using (Bool; false; true; _∧_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Types
open import Core.Semantics.Containers
open import Core.Semantics.Inductive

----------------------------------------------------------------------
-- Interpretation of the shared type codes
----------------------------------------------------------------------

code : ∀ {mode n} → Ty mode n → Container n
code `𝟘         = zeroC
code `𝟙         = oneC
code (T `× U) = code T ×C code U
code (T `+ U) = code T +C code U
code (T `⇒ U) = expC (code T) (code U)
code (` i)     = varC i
code (ind G)   = muC (code G)

-- Open codes are container extensions.  Closed types are represented by
-- shapes, so products, sums, and exponentials compute to the corresponding
-- Agda type constructors without an irrelevant Fin 0 hole assignment.
⟦_⟧ : ∀ {mode n} → Ty mode n → (Fin n → Set) → Set
⟦ T ⟧ ρ = Value (code T) ρ

⟦_⟧₀ : ∀ {mode} → TY mode → Set
⟦ T ⟧₀ = Shape (code T)

----------------------------------------------------------------------
-- Decidable guardedness and well-formed type codes
----------------------------------------------------------------------

-- The recursive variable must occur below a data constructor.  An outer
-- product, sum, or nested inductive type supplies the required guard; a
-- positive exponential does not.
guarded : ∀ {mode n} → Ty mode (suc n) → Bool
guarded `𝟘           = true
guarded `𝟙           = true
guarded (T `× U)   = true
guarded (T `+ U)   = true
guarded (T `⇒ U)   = guarded U
guarded (` zero)    = false
guarded (` (suc i)) = true
guarded (ind G)     = true

Guarded : ∀ {mode n} → Ty mode (suc n) → Set
Guarded G = guarded G ≡ true

-- Guarded only checks the variable bound by the immediately surrounding
-- ind.  wellFormed also checks every nested inductive type in the code.
wellFormed : ∀ {mode n} → Ty mode n → Bool
wellFormed `𝟘         = true
wellFormed `𝟙         = true
wellFormed (T `× U) = wellFormed T ∧ wellFormed U
wellFormed (T `+ U) = wellFormed T ∧ wellFormed U
wellFormed (T `⇒ U) = wellFormed T ∧ wellFormed U
wellFormed (` i)     = true
wellFormed (ind G)   = guarded G ∧ wellFormed G

WellFormed : ∀ {mode n} → Ty mode n → Set
WellFormed T = wellFormed T ≡ true

-- CheckedTy is the validated formation judgement.  Keeping raw Ty separate
-- makes renaming and substitution simple; clients call validate at the
-- language boundary rather than silently assuming guardedness.
CheckedTy : Mode → ℕ → Set
CheckedTy mode n = Σ (Ty mode n) WellFormed

validate : ∀ {mode n} → Ty mode n → Maybe (CheckedTy mode n)
validate T with wellFormed T in equation
... | true  = just (T , equation)
... | false = nothing

----------------------------------------------------------------------
-- Polynomial/finitary versus exponential/possibly infinitary codes
----------------------------------------------------------------------

-- Syntactic polynomiality excludes exponentials.  Every FO code is
-- polynomial; HO exponentials may introduce infinitely many positions.
data Polynomial : ∀ {mode n} → Ty mode n → Set where
  poly-𝟘   : ∀ {mode n} → Polynomial (`𝟘 {md = mode} {n = n})
  poly-𝟙   : ∀ {mode n} → Polynomial (`𝟙 {md = mode} {n = n})
  poly-× : ∀ {mode n} {T U : Ty mode n} →
           Polynomial T → Polynomial U → Polynomial (T `× U)
  poly-+ : ∀ {mode n} {T U : Ty mode n} →
           Polynomial T → Polynomial U → Polynomial (T `+ U)
  poly-` : ∀ {mode n} {i : Fin n} → Polynomial (` {md = mode} i)
  poly-ind : ∀ {mode n} {G : Ty mode (suc n)} →
             Polynomial G → Polynomial (ind G)

fo-polynomial : ∀ {n} (T : Ty FO n) → Polynomial T
fo-polynomial `𝟘         = poly-𝟘
fo-polynomial `𝟙         = poly-𝟙
fo-polynomial (T `× U) = poly-× (fo-polynomial T) (fo-polynomial U)
fo-polynomial (T `+ U) = poly-+ (fo-polynomial T) (fo-polynomial U)
fo-polynomial (` i)     = poly-`
fo-polynomial (ind G)   = poly-ind (fo-polynomial G)
