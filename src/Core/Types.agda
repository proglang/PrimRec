{-# OPTIONS --safe #-}

module Core.Types where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)

----------------------------------------------------------------------
-- Type codes shared by the first- and higher-order calculi
----------------------------------------------------------------------

data Mode : Set where
  FO HO : Mode

infixr 7 _`×_
infixr 8 _`+_
infixr 9 _`⇒_

data Ty : Mode → ℕ → Set where
  `𝟘 `𝟙 : ∀ {mode n} → Ty mode n
  _`×_ : ∀ {mode n} → Ty mode n → Ty mode n → Ty mode n
  _`+_ : ∀ {mode n} → Ty mode n → Ty mode n → Ty mode n
  _`⇒_ : ∀ {n} → Ty HO 0 → Ty HO n → Ty HO n
  `    : ∀ {mode n} → Fin n → Ty mode n
  ind  : ∀ {mode n} → Ty mode (suc n) → Ty mode n

TY : Mode → Set
TY mode = Ty mode 0

FO-TY : Set
FO-TY = TY FO

HO-TY : Set
HO-TY = TY HO

variable
  mode : Mode
  n m o : ℕ

----------------------------------------------------------------------
-- Renaming and substitution of type variables
----------------------------------------------------------------------

Ren : ℕ → ℕ → Set
Ren n m = Fin n → Fin m

extᴿ : Ren n m → Ren (suc n) (suc m)
extᴿ ρ zero    = zero
extᴿ ρ (suc i) = suc (ρ i)

ren : Ren n m → Ty mode n → Ty mode m
ren ρ `𝟘         = `𝟘
ren ρ `𝟙         = `𝟙
ren ρ (T `× U) = ren ρ T `× ren ρ U
ren ρ (T `+ U) = ren ρ T `+ ren ρ U
ren ρ (T `⇒ U) = T `⇒ ren ρ U
ren ρ (` i)     = ` (ρ i)
ren ρ (ind G)   = ind (ren (extᴿ ρ) G)

Sub : Mode → ℕ → ℕ → Set
Sub mode n m = Fin n → Ty mode m

extˢ : Sub mode n m → Sub mode (suc n) (suc m)
extˢ σ zero    = ` zero
extˢ σ (suc i) = ren suc (σ i)

sub : Sub mode n m → Ty mode n → Ty mode m
sub σ `𝟘         = `𝟘
sub σ `𝟙         = `𝟙
sub σ (T `× U) = sub σ T `× sub σ U
sub σ (T `+ U) = sub σ T `+ sub σ U
sub σ (T `⇒ U) = T `⇒ sub σ U
sub σ (` i)     = σ i
sub σ (ind G)   = ind (sub (extˢ σ) G)

ids : Sub mode n n
ids i = ` i

push : Sub mode n m → Ty mode m → Sub mode (suc n) m
push σ T zero    = T
push σ T (suc i) = σ i

σ₀ : Ty mode n → Sub mode (suc n) n
σ₀ T = push ids T

infix 9 _⇐_

_⇐_ : Ty mode (suc n) → Ty mode n → Ty mode n
G ⇐ T = sub (σ₀ T) G

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
