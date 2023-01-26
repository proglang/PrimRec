\begin{code}[hide]
module PR-HTrees where

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; suc; zero; _*_; _+_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head; concat)
open import Data.Vec.Properties using (lookup-map)
open import Data.List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_; _++_ to _++ᴸ_; length to lengthᴸ; map to mapᴸ)
open import Function using (_∘_)

open import Utils
\end{code}
\newcommand\PRHTreesSorted{
\begin{code}
record Sorted (S : Set) : Set₁ where
  constructor mkSorted
  field
    {symbols} : Set
    rank : symbols → ℕ
    sin* : (a : symbols) → Vec S (rank a)
    sout : symbols → S
\end{code}
}
\begin{code}[hide]
open Sorted public
\end{code}
\newcommand\PRHTreesTerm{
\begin{code}
data Term* {S} (Sig : Sorted S) : Vec S n → Set
data Term  (Sig : Sorted S) : S → Set where
  con : (a : symbols Sig) → Term* Sig (sin* Sig a) → Term Sig (sout Sig a)

data Term* {S} Sig where
  []  : Term* Sig []
  _∷_ : ∀ {s₀}{s* : Vec S n} → Term Sig s₀ → Term* Sig s* → Term* Sig (s₀ ∷ s*)
\end{code}
}
\begin{code}[hide]
data PR* {S} (Sig : Sorted S) {n : ℕ} : Vec S n × Vec S m → Set
\end{code}
\newcommand\PRHTreesDefinition{
\begin{code}
data PR (Sig : Sorted S) : Vec S n × S → Set where
  σ : (a : symbols Sig) → PR Sig ⟨ sin* Sig a , sout Sig a ⟩
  π : ∀ {s* : Vec S n} → (i : Fin n) → PR Sig ⟨ s* , lookup s* i ⟩
  C : ∀ {s m} {ss′ : Vec S m} {ss : Vec S n}
    → (f  : PR Sig ⟨ ss′ , s ⟩)
    → (g* : PR* Sig ⟨ ss , ss′ ⟩)
    → PR Sig ⟨ ss , s ⟩
  P : ∀ {s₀}{ss : Vec S n}
    → (res : S → S)
    → (h : (a : symbols Sig)
         → PR Sig ⟨ (map res (sin* Sig a) ++ sin* Sig a) ++ ss , res (sout Sig a) ⟩)
    → PR Sig ⟨ s₀ ∷ ss , res s₀ ⟩
\end{code}
}
\begin{code}[hide]
data PR* {S} Sig where
  []  : ∀ {ssin} → PR* Sig ⟨ ssin , [] ⟩
  _∷_ : ∀ {ssin}{s₀}{ssout : Vec S m} → PR Sig ⟨ ssin , s₀ ⟩ → PR* Sig ⟨ ssin , ssout ⟩ → PR* Sig ⟨ ssin , s₀ ∷ ssout ⟩
\end{code}
\newcommand\PRHTreesAlookup{
\begin{code}
alookup : ∀ {Sig} {ssin : Vec S n}
  → Term* Sig ssin → (i : Fin n) → Term Sig (lookup ssin i)
\end{code}
}
\begin{code}[hide]
alookup (x ∷ _) zero = x
alookup (_ ∷ v*) (suc i) = alookup v* i
\end{code}
\newcommand\PRHTreesAppend{
\begin{code}
_++ᴬ_ : ∀ {Sig} {ss₁ : Vec S m} {ss₂ : Vec S n}
  → Term* Sig ss₁ → Term* Sig ss₂ → Term* Sig (ss₁ ++ ss₂)
\end{code}
}
\begin{code}[hide]
[] ++ᴬ w* = w*
(x ∷ v*) ++ᴬ w* = x ∷ (v* ++ᴬ w*)
\end{code}
\newcommand\PRHTreesMap{
\begin{code}
mapᴬ : ∀ {Sig} {ss : Vec S n} {res : S → S}
  → (∀ (i : Fin n) → Term Sig (lookup ss i) → Term Sig (res (lookup ss i)))
  → Term* Sig ss → Term* Sig (map res ss)
mapᴬ f [] = []
mapᴬ f (v ∷ v*) = (f Fin.zero v) ∷ (mapᴬ (f ∘ Fin.suc) v*)
\end{code}
}
\begin{code}[hide]
{-# TERMINATING #-}
eval* : ∀ {Sig}{ssin : Vec S n}{ssout : Vec S m} → PR* Sig ⟨ ssin , ssout ⟩ → Term* Sig ssin → Term* Sig ssout
\end{code}
\newcommand\PRHTreesEval{
\begin{code}
eval  : ∀ {Sig}{ssin : Vec S n}{sout : S}
  → PR Sig ⟨ ssin , sout ⟩
  → Term* Sig ssin → Term Sig sout

eval (σ a)     v* = con a v*
eval (π i)     v* = alookup v* i
eval (C f g*)  v* = eval f (eval* g* v*)
eval (P res h) (con a x* ∷ v*) = eval (h a) ((mapᴬ (λ _ x → eval (P res h) (x ∷ v*)) x* ++ᴬ x*) ++ᴬ v*)
\end{code}
}
\begin{code}[hide]
eval* []       v* = []
eval* (p ∷ p*) v* = eval p v* ∷ eval* p* v*
\end{code}
\begin{code}[hide]
data PR′ (Sig : Sorted S) : Vec S n × S → Set where
  P′ : ∀ {s₀}{ss : Vec S n}
    → (res : S → S)
    → (h : (a : symbols Sig) → PR′ Sig ⟨ concat (map (λ s → [ res s , s ]) (sin* Sig a)) ++ ss , res (sout Sig a) ⟩)
    → PR′ Sig ⟨ s₀ ∷ ss , res s₀ ⟩

concmapᴬ : ∀ {Sig} {ss : Vec S n} {res : S → S}
  → (∀ {i : Fin n} → Term Sig (lookup ss i) → Term Sig (res (lookup ss i)) × Term Sig (lookup ss i))
  → Term* Sig ss → Term* Sig (concat (map (λ s → [ res s , s ]) ss))
concmapᴬ f [] = []
concmapᴬ f (v ∷ v*) with f {Fin.zero} v
... | ⟨ fv , v ⟩ = fv ∷ (v ∷ (concmapᴬ (λ{i} → f {Fin.suc i}) v*))

{-# TERMINATING #-}
eval′ : ∀ {Sig}{ssin : Vec S n}{sout : S} → PR′ Sig ⟨ ssin , sout ⟩ → Term* Sig ssin → Term Sig sout
eval′ (P′ res h) (con a xs ∷ v*) = eval′ (h a) (concmapᴬ (λ x → ⟨ (eval′ (P′ res h) (x ∷ v*)) , x ⟩) xs ++ᴬ v*)
\end{code}
