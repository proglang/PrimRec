{-# OPTIONS --safe #-}

module Core.Types where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)

----------------------------------------------------------------------
-- Type codes shared by the first- and higher-order calculi
----------------------------------------------------------------------

--! CoreTypesGrammar {
data Mode : Set where
  FO HO : Mode

infixr 7 _`×_
infixr 8 _`+_
infixr 9 _`⇒_

data Ty : Mode → ℕ → Set where
  `𝟘 `𝟙  : ∀ {md n} → Ty md n
  _`×_   : ∀ {md n} → Ty md n → Ty md n → Ty md n
  _`+_   : ∀ {md n} → Ty md n → Ty md n → Ty md n
  _`⇒_   : ∀ {n} → Ty HO 0 → Ty HO n → Ty HO n
  `      : ∀ {md n} → Fin n → Ty md n
  ind    : ∀ {md n} → Ty md (suc n) → Ty md n

TY : Mode → Set
TY md = Ty md 0
--! }

variable
  md : Mode
  n m o : ℕ

----------------------------------------------------------------------
-- Renaming and substitution of type variables
----------------------------------------------------------------------

Ren : ℕ → ℕ → Set
Ren n m = Fin n → Fin m

extᴿ : Ren n m → Ren (suc n) (suc m)
extᴿ ρ zero    = zero
extᴿ ρ (suc i) = suc (ρ i)

ren : Ren n m → Ty md n → Ty md m
ren ρ `𝟘         = `𝟘
ren ρ `𝟙         = `𝟙
ren ρ (T `× U) = ren ρ T `× ren ρ U
ren ρ (T `+ U) = ren ρ T `+ ren ρ U
ren ρ (T `⇒ U) = T `⇒ ren ρ U
ren ρ (` i)     = ` (ρ i)
ren ρ (ind G)   = ind (ren (extᴿ ρ) G)

Sub : Mode → ℕ → ℕ → Set
Sub md n m = Fin n → Ty md m

extˢ : Sub md n m → Sub md (suc n) (suc m)
extˢ σ zero    = ` zero
extˢ σ (suc i) = ren suc (σ i)

sub : Sub md n m → Ty md n → Ty md m
sub σ `𝟘         = `𝟘
sub σ `𝟙         = `𝟙
sub σ (T `× U) = sub σ T `× sub σ U
sub σ (T `+ U) = sub σ T `+ sub σ U
sub σ (T `⇒ U) = T `⇒ sub σ U
sub σ (` i)     = σ i
sub σ (ind G)   = ind (sub (extˢ σ) G)

ids : Sub md n n
ids i = ` i

push : Sub md n m → Ty md m → Sub md (suc n) m
push σ T zero    = T
push σ T (suc i) = σ i

σ₀ : Ty md n → Sub md (suc n) n
σ₀ T = push ids T

infix 9 _[_]

_[_] : Ty md (suc n) → Ty md n → Ty md n
G [ T ] = sub (σ₀ T) G

----------------------------------------------------------------------
-- The first-order fragment embeds structurally into the HO type codes.
----------------------------------------------------------------------

lift : Ty FO n → Ty HO n
lift `𝟘         = `𝟘
lift `𝟙         = `𝟙
lift (T `× U) = lift T `× lift U
lift (T `+ U) = lift T `+ lift U
lift (` i)     = ` i
lift (ind G)   = ind (lift G)
