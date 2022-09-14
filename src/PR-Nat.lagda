\begin{code}[hide]
module PR-Nat where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head)

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Utils

----------------------------------------------------------------------
-- primitive recursion on ℕ
----------------------------------------------------------------------
\end{code}
The datatype \APR{n} defines an abstract syntax for $n$-ary primitive recursive functions.
The type \AFin{n} comprises the elements $\{0, 1, \dots, n-1\}$.
The type \AVec{A}{n} contains vectors of size $n$ with elements of type $A$.
\begin{code}
data PR : ℕ → Set where
  Z : PR n                      -- zero
  σ : PR (suc zero)             -- successor
  π : (i : Fin n)               -- i-th projection
    → PR n
  C : (f : PR m)                -- composition
    → (g* : Vec (PR n) m)
    → PR n
  P : (g : PR n)                -- primitive recursion
    → (h : PR (suc (suc n)))
    → PR (suc n)
\end{code}
The function \AgdaFunction{eval} maps a pr function to its semantics.
We represent ${ℕ}^n$ by the vector type \AVec{ℕ}n.
\begin{code}
eval  : PR n → (Vec ℕ n → ℕ)
eval* : Vec (PR n) m → Vec ℕ n → Vec ℕ m

eval Z        v*           = 0
eval σ        [ x ]        = suc x
eval (π i)    v*           = lookup v* i
eval (C f g*) v*           = eval f (eval* g* v*)
eval (P g h)  (zero ∷ v*)  = eval g v*
eval (P g h)  (suc x ∷ v*) = eval h ((eval (P g h) (x ∷ v*)) ∷ (x ∷ v*))

eval* []       v*          = []
eval* (p ∷ p*) v*          = eval p v*  ∷ eval* p* v*
\end{code}
The function \AgdaFunction{eval*} can be expressed as a map over the function of functions, alas the termination checker does not accept this definition.
\begin{code}
eval*≡map-eval : ∀ (p* : Vec (PR n) m) (v* : Vec ℕ n) → eval* p* v* ≡ map (λ p → eval p v*) p*
eval*≡map-eval [] v* = refl
eval*≡map-eval (p ∷ p*) v* rewrite eval*≡map-eval p* v* = refl
\end{code}
