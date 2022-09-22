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
This concept translates directly to Agda where \Arank{a}, \Asin{a}, and \Asout{a} are the rank, the input sorts, and the output sort of symbol $a$.
\begin{code}
record Sorted (S : Set) : Set₁ where
  constructor mkSorted
  field
    {symbols} : Set
    rank : symbols → ℕ
    sin* : (a : symbols) → Vec S (rank a)
    sout : symbols → S
open Sorted public
\end{code}
The definition of the term algebra is conceptually the same as before, but there is additional complication due to the sorting.
\begin{code}
data Term* {S} (Sig : Sorted S) : Vec S n → Set
data Term  (Sig : Sorted S) : S → Set where
  con : (a : symbols Sig) → Term* Sig (sin* Sig a) → Term Sig (sout Sig a)

data Term* {S} Sig where
  []  : Term* Sig []
  _∷_ : ∀ {s₀}{s* : Vec S n} → Term Sig s₀ → Term* Sig s* → Term* Sig (s₀ ∷ s*)
\end{code}
In principle, \ATerms{Sig\ s*} is just a vector of terms, but each element has a different type as indicated by \AgdaGeneralizable{s*}.
While one can define a suitably indexed heterogeneous vector type, say \AHVec{F}{s*}, where $F :$ S → {\ASet} and $s*$ : \AVec{S}{n}, this type creates new problems.
To see this, consider the type of the second argument of {\Acon}, which would have to be \AHVec{(\ATerm{Sig})}{(\Asin{Sig} a)}.
Unfortunately, this type is not accepted as it (formally) violates the requirement that datatypes definitions are strictly positive. Hence, the split into \ATerm{Sig\ s} and \ATerms{Sig\ s*}.

The same issue arises in the definition of the abstract syntax for primitive recursion, but we exclude the details.
\begin{code}[hide]
data PR* {S} (Sig : Sorted S) {n : ℕ} : Vec S n × Vec S m → Set
\end{code}
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
\begin{code}[hide]
data PR* {S} Sig where
  []  : ∀ {ssin} → PR* Sig ⟨ ssin , [] ⟩
  _∷_ : ∀ {ssin}{s₀}{ssout : Vec S m} → PR Sig ⟨ ssin , s₀ ⟩ → PR* Sig ⟨ ssin , ssout ⟩ → PR* Sig ⟨ ssin , s₀ ∷ ssout ⟩
\end{code}
The interesting part is the definition of the {\AP} constructor.
The function \AgdaBound{res} maps the sort of the recursion argument to the return sort---all further arguments are passed through the recursion unchanged so they should not affect the return sort.
The function \AgdaBound{h} maps a symbol $a$ to a pr function that takes the results of the recursive calls on the subterms of $a$, then the subterms themselves, and finally the further, pass-through arguments to produce a result determined by the return sort determined by the sort of $a$.

Evaluation is analogous to evaluation for trees, but there are some additional twists to handle heterogeneous vectors of type \ATerms{sig\ s*}.
We need lookup, concatenation, and a map function for heterogeneous vectors.
The first two are straightforward to define, but the latter is worth some discussion.
\begin{code}
alookup : ∀ {Sig} {ssin : Vec S n}
  → Term* Sig ssin → (i : Fin n) → Term Sig (lookup ssin i)
\end{code}
\begin{code}[hide]
alookup (x ∷ _) zero = x
alookup (_ ∷ v*) (suc i) = alookup v* i
\end{code}
\begin{code}
_++ᴬ_ : ∀ {Sig} {ss₁ : Vec S m} {ss₂ : Vec S n}
  → Term* Sig ss₁ → Term* Sig ss₂ → Term* Sig (ss₁ ++ ss₂)
\end{code}
\begin{code}[hide]
[] ++ᴬ w* = w*
(x ∷ v*) ++ᴬ w* = x ∷ (v* ++ᴬ w*)
\end{code}
\begin{code}
mapᴬ : ∀ {Sig} {ss : Vec S n} {res : S → S}
  → (∀ (i : Fin n) → Term Sig (lookup ss i) → Term Sig (res (lookup ss i)))
  → Term* Sig ss → Term* Sig (map res ss)
mapᴬ f [] = []
mapᴬ f (v ∷ v*) = (f Fin.zero v) ∷ (mapᴬ (f ∘ Fin.suc) v*)
\end{code}
Mapping over a heterogeneous vector like \ATerms{Sig\ ss} requires a family of functions, rather than a single one as for vectors or lists, and a way to predict the heterogeneous return type.
We address the latter using the result type function \AgdaBound{res}.
The former is addressed by having the \AgdaFunction{mapᴬ} function take an indexed function.
Given the index $i$, we can calculate the required function type from the sort vector \AgdaBound{ss} and the result function \AgdaBound{res}.

Given all these tools and the explanation of the \AP{} constructor, the definition of the semantics is a simple generalization of previous definitions.
\begin{code}[hide]
{-# TERMINATING #-}
eval* : ∀ {Sig}{ssin : Vec S n}{ssout : Vec S m} → PR* Sig ⟨ ssin , ssout ⟩ → Term* Sig ssin → Term* Sig ssout
\end{code}
\begin{code}
eval  : ∀ {Sig}{ssin : Vec S n}{sout : S}
  → PR Sig ⟨ ssin , sout ⟩
  → Term* Sig ssin → Term Sig sout

eval (σ a)     v* = con a v*
eval (π i)     v* = alookup v* i
eval (C f g*)  v* = eval f (eval* g* v*)
eval (P res h) (con a x* ∷ v*) = eval (h a) ((mapᴬ (λ _ x → eval (P res h) (x ∷ v*)) x* ++ᴬ x*) ++ᴬ v*)
\end{code}
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
