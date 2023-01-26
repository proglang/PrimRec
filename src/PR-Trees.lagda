\begin{code}[hide]
module PR-Trees where

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
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
\begin{code}[hide]
module obsolete where
  Rank : Set → Set
  Rank A = A → ℕ

  data PRR (r : Rank A) : ℕ → Set where
    σ : (a : A) → PRR r (r a)
    π : (i : Fin n) → PRR r n
    C : (f : PRR r m) → (g : Vec (PRR r n) m) → PRR r n
    P : (h : (a : A) → PRR r (r a + r a + n)) → PRR r (suc n)

  data Alg (r : Rank A) : Set where
    con : (a : A) → Vec (Alg r) (r a) → Alg r

  {-# TERMINATING #-}
  eval  : ∀ {r : Rank A} → PRR r n → Vec (Alg r) n → Alg r
  eval* : ∀ {r : Rank A} → Vec (PRR r n) m → Vec (Alg r) n → Vec (Alg r) m

  eval (σ a) v* = con a v*
  eval (π i) v* = lookup v* i
  eval (C f g*) v* = eval f (eval* g* v*)
  eval {r = r} (P h) (con a xs ∷ v*) = eval (h a) ((map (λ x → eval (P h) (x ∷ v*)) xs ++ xs) ++ v* )

  eval* [] v* = []
  eval* (x ∷ p*) v* = (eval x v*) ∷ (eval* p* v*)
\end{code}
\newcommand\PRTreesRanked{
\begin{code}
record Ranked : Set₁ where
  constructor mkRanked
  field
    {symbols} : Set
    rank : symbols → ℕ
\end{code}
}
\begin{code}[hide]
open Ranked public
\end{code}
\newcommand\PRTreesTerm{
\begin{code}
data Term R : Set where
  con : (a : symbols R) → Vec (Term R) (rank R a) → Term R
\end{code}
}
\newcommand\PRTreesDefinition{
\begin{code}
data PR R : ℕ → Set where
  σ : (a : symbols R) → PR R (rank R a)
  π : (i : Fin n) → PR R n
  C : (f : PR R m) → (g* : Vec (PR R n) m) → PR R n
  P : (h : (a : symbols R) → PR R (rank R a + rank R a + n)) → PR R (suc n)
\end{code}
}
\begin{code}[hide]
variable
  R : Ranked

{-# TERMINATING #-}
eval* : Vec (PR R n) m → Vec (Term R) n → Vec (Term R) m
\end{code}
\newcommand\PRTreesEval{
\begin{code}
eval  : PR R n → Vec (Term R) n → Term R
eval (σ a) v* = con a v*
eval (π i) v* = lookup v* i
eval (C f g*) v* = eval f (eval* g* v*)
eval (P h) (con a xs ∷ v*) = eval (h a) (((map (λ x → eval (P h) (x ∷ v*)) xs) ++ xs) ++ v*)
\end{code}
}
\begin{code}[hide]
eval* [] v* = []
eval* (p ∷ p*) v* = eval p v* ∷ eval* p* v*
\end{code}
\begin{code}[hide]
data PR′ R : ℕ → Set where
  P′ : (h : (a : symbols R) → PR′ R (rank R a * 2 + n)) → PR′ R (suc n)
{-# TERMINATING #-}
eval′ : PR′ R n → Vec (Term R) n → Term R
eval′ (P′ h) (con a xs ∷ v*) = eval′ (h a) ((concat (map (λ x → [ eval′ (P′ h) (x ∷ v*) , x ]) xs)) ++ v*)
\end{code}
