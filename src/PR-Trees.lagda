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
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head)
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
We can express the concept of a ranked alphabet literally in Agda. 
\begin{code}
record Ranked : Set₁ where
  constructor mkRanked
  field
    symbols : Set
    rank : symbols → ℕ
open Ranked
\end{code}
The set of terms over a ranked alphabet $R : \ARanked$ is also called the term algebra over $R$.
To construct a term, we need a symbol $a$ and as many terms as indicated by the rank of $a$.
\begin{code}
data Term R : Set where
  con : (a : symbols R) → Vec (Term R) (rank R a) → Term R
\end{code}

The syntax of pr functions gets simpler for terms as we do not have to make amends for a special $0$-function.
Instead, there is a family of constructor operators $σ$, which is indexed by a symbol $a∈A$ and the arity of which is determined by the rank of $a$. Projection and composition remain as before, but primitive recursion generalizes.
Instead of distinguishing between $g$-functions and $h$-functions, there is a single $A$-indexed family of functions $h$.
The function constructed by primitive recursion on the family $h$ takes $n+1$ arguments with the first argument being the designated recursion argument.
The function $h_a$ handles recursion on terms starting with $a$ of rank $r_a$, say.
As there are $r_a$ subterms, the results of $r_a$ recursive invocations, the $r_a$ subterms, and the remaining $n$ are arguments of $h_a$.
Consequently, $h_a$ takes $r_a + r_a + n$ arguments.
\begin{code}
data PR R : ℕ → Set where
  σ : (a : symbols R) → PR R (rank R a)
  π : (i : Fin n) → PR R n
  C : (f : PR R m) → (g* : Vec (PR R n) m) → PR R n
  P : (h : (a : symbols R) → PR R (rank R a + rank R a + n)) → PR R (suc n)
\end{code}
\begin{code}[hide]
variable
  R : Ranked

{-# TERMINATING #-}
eval* : Vec (PR R n) m → Vec (Term R) n → Vec (Term R) m
\end{code}
The definition of the semantics follows the explanation precisely.
\begin{code}
eval  : PR R n → Vec (Term R) n → Term R
eval (σ a) v* = con a v*
eval (π i) v* = lookup v* i
eval (C f g*) v* = eval f (eval* g* v*)
eval (P h) (con a xs ∷ v*) = eval (h a) (((map (λ x → eval (P h) (x ∷ v*)) xs) ++ xs) ++ v*)
\end{code}
\begin{code}[hide]
eval* [] v* = []
eval* (p ∷ p*) v* = eval p v* ∷ eval* p* v*
\end{code}
