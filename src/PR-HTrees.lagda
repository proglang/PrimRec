\begin{code}
module PR-HTrees where

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; suc; zero; _*_; _+_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head)
open import Data.Vec.Properties using (lookup-map)
open import Data.List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_; _++_ to _++ᴸ_; length to lengthᴸ; map to mapᴸ)
open import Function using (_∘_)

open import Utils

record Sorted (S : Set) : Set₁ where
  constructor mkSorted
  field
    symbols : Set
    rank    : symbols → ℕ
    sortin  : (a : symbols) → Vec S (rank a)
    sortout : symbols → S
open Sorted

data Alg* {S} (Sig : Sorted S) : Vec S n → Set
data Alg  (Sig : Sorted S) : S → Set where
  con : (a : symbols Sig) → Alg* Sig (sortin Sig a) → Alg Sig (sortout Sig a)

data Alg* {S} Sig where
  []  : Alg* Sig []
  _∷_ : ∀ {s₀}{s* : Vec S n} → Alg Sig s₀ → Alg* Sig s* → Alg* Sig (s₀ ∷ s*)


data PR* {S} (Sig : Sorted S) {n : ℕ} : Vec S n × Vec S m → Set
data PR (Sig : Sorted S) : Vec S n × S → Set where
  σ : (a : symbols Sig) → PR Sig ⟨ sortin Sig a , sortout Sig a ⟩
  π : ∀ {s* : Vec S n} → (i : Fin n) → PR Sig ⟨ s* , lookup s* i ⟩
  C : ∀ {s m} {ss′ : Vec S m} {ss : Vec S n}
    → (g  : PR Sig ⟨ ss , s ⟩)
    → (f* : PR* Sig ⟨ ss , ss′ ⟩)
    → PR Sig ⟨ ss′ , s ⟩
  P : ∀ {s₀}{ss : Vec S n}
    → (res : S → S)
    → (h : (a : symbols Sig) → PR Sig ⟨ map res (sortin Sig a) ++ sortin Sig a ++ ss , res (sortout Sig a) ⟩)
    → PR Sig ⟨ s₀ ∷ ss , res s₀ ⟩

data PR* {S} Sig where
  []  : ∀ {ssin} → PR* Sig ⟨ ssin , [] ⟩
  _∷_ : ∀ {ssin}{s₀}{ssout : Vec S m} → PR Sig ⟨ ssin , s₀ ⟩ → PR* Sig ⟨ ssin , ssout ⟩ → PR* Sig ⟨ ssin , s₀ ∷ ssout ⟩

\end{code}
