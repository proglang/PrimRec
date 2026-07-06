\begin{code}[hide]
{-# OPTIONS --safe #-}
module PR-Nat where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head)

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Utils

----------------------------------------------------------------------
-- primitive recursion on ℕ
----------------------------------------------------------------------
\end{code}
\newcommand\PRNat{
\begin{code}
data PR : ℕ → Set where
  Z : PR 0                      -- zero
  σ : PR 1                      -- successor
  π : (i : Fin n)               -- i-th projection
    → PR n
  C : (f : PR m)                -- composition
    → (g* : Vec (PR n) m)
    → PR n
  Pr : (g : PR n)                -- primitive recursion
    → (h : PR (2 + n))
    → PR (1 + n)
\end{code}
}
\begin{code}[hide]
  Ct : (g : PR n)                -- catamorphism over nat, can be simulated with Pr
    → (h : PR (1 + n))
    → PR (1 + n)

para : (Vec ℕ n → ℕ) → (Vec ℕ (2 + n) → ℕ) → (Vec ℕ (1 + n) → ℕ)
para g h (zero ∷ v*) = g v*
para g h (suc x ∷ v*) = h (para g h (x ∷ v*) ∷ x ∷ v*)

allFin : (n : ℕ) → Vec (Fin n) n
allFin zero = []
allFin (suc n) = zero ∷ map suc (allFin n)

dropCounter : (n : ℕ) → Vec (PR (2 + n)) (1 + n)
dropCounter n = π zero ∷ map (λ i → π (suc (suc i))) (allFin n)

Ct⇒Pr : PR n → PR (1 + n) → PR (1 + n)
Ct⇒Pr {n} g h = Pr g (C h (dropCounter n))
\end{code}
\newcommand\PRNatEval{
\begin{code}
eval  : PR n → (Vec ℕ n → ℕ)
eval* : Vec (PR n) m → Vec ℕ n → Vec ℕ m

eval* []       v*          = []
eval* (p ∷ p*) v*          = eval p v*  ∷ eval* p* v*

eval Z        []           = 0
eval σ        [ x ]        = suc x
eval (π i)    v*           = lookup v* i
eval (C f g*) v*           = eval f (eval* g* v*)
eval (Pr g h)  (zero ∷ v*)  = eval g v*
eval (Pr g h)  (suc x ∷ v*) = eval h ((eval (Pr g h) (x ∷ v*)) ∷ (x ∷ v*))
\end{code}
}
\begin{code}[hide]
eval (Ct g h)  (zero ∷ v*)  = eval g v*
eval (Ct g h)  (suc x ∷ v*) = eval h ((eval (Ct g h) (x ∷ v*)) ∷ v*)

eval*-projections : ∀ (is : Vec (Fin n) m) (v* : Vec ℕ n)
  → eval* (map π is) v* ≡ map (lookup v*) is
eval*-projections [] v* = refl
eval*-projections (i ∷ is) v* rewrite eval*-projections is v* = refl

lookup-allFin : ∀ (v* : Vec ℕ n) → map (lookup v*) (allFin n) ≡ v*
lookup-allFin [] = refl
lookup-allFin (x ∷ v*)
  rewrite ∘-map (lookup (x ∷ v*)) suc (allFin _)
        | lookup-allFin v* = refl

eval*-dropCounter : ∀ (v* : Vec ℕ n) acc counter
  → eval* (dropCounter n) (acc ∷ counter ∷ v*) ≡ acc ∷ v*
eval*-dropCounter {n} v* acc counter
  rewrite sym (∘-map π (λ i → suc (suc i)) (allFin n))
        | eval*-projections (map (λ i → suc (suc i)) (allFin n)) (acc ∷ counter ∷ v*)
        | ∘-map (lookup (acc ∷ counter ∷ v*)) (λ i → suc (suc i)) (allFin n)
        | lookup-allFin v* = refl

Ct⇒Pr-sound : ∀ (g : PR n) (h : PR (1 + n)) (v* : Vec ℕ (1 + n))
  → eval (Ct g h) v* ≡ eval (Ct⇒Pr g h) v*
Ct⇒Pr-sound g h (zero ∷ v*) = refl
Ct⇒Pr-sound {n} g h (suc x ∷ v*)
  rewrite Ct⇒Pr-sound g h (x ∷ v*)
        | eval*-dropCounter v* (eval (Ct⇒Pr g h) (x ∷ v*)) x = refl

eval*≡map-eval : ∀ (p* : Vec (PR n) m) (v* : Vec ℕ n) → eval* p* v* ≡ map (λ p → eval p v*) p*
eval*≡map-eval [] v* = refl
eval*≡map-eval (p ∷ p*) v* rewrite eval*≡map-eval p* v* = refl
\end{code}
