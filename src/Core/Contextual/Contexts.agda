{-# OPTIONS --safe #-}

module Core.Contextual.Contexts where

open import Data.List using (List; []; _∷_)
open import Core.Types
open import Core.Contextual.PRHO

Ctx : Set
Ctx = List (TY HO)

⟦_⟧ᶜ : Ctx → TY HO
⟦ [] ⟧ᶜ      = `𝟙
⟦ A ∷ Γ ⟧ᶜ = ⟦ Γ ⟧ᶜ `× A

Tm : Ctx → TY HO → Set
Tm Γ A = ⟦ Γ ⟧ᶜ ⊢ A

data Var : Ctx → TY HO → Set where
  zero : ∀ {Γ A} → Var (A ∷ Γ) A
  suc  : ∀ {Γ A B} → Var Γ A → Var (B ∷ Γ) A

weaken : ∀ {Γ A B} → Tm Γ A → Tm (B ∷ Γ) A
weaken t = cut t fst

lookup : ∀ {Γ A} → Var Γ A → Tm Γ A
lookup zero    = snd
lookup (suc i) = weaken (lookup i)

lam : ∀ {Γ A B} → Tm (A ∷ Γ) B → Tm Γ (A `⇒ B)
lam = curry

app : ∀ {Γ A B} → Tm Γ (A `⇒ B) → Tm Γ A → Tm Γ B
app f x = cut eval (pair f x)
