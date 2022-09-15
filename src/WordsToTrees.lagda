\begin{code}[hide]
module WordsToTrees where

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)
open import Data.Maybe using (Maybe; nothing; just; maybe)
open import Data.Nat using (ℕ; suc; zero; _*_; _+_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head)
open import Data.Vec.Properties using (lookup-map)
open import Data.List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_; _++_ to _++ᴸ_; length to lengthᴸ; map to mapᴸ)
open import Function using (_∘_; const)

open import Utils

import PR-Words as Words
import PR-Trees as Trees
\end{code}
\begin{code}
make-R : ∀ A → Trees.Ranked
make-R A = Trees.mkRanked (Maybe A) (maybe (const 1) 0)

⟦_⟧ⱽ : List A → Trees.Term (make-R A)
⟦ []ᴸ ⟧ⱽ     = Trees.con nothing []
⟦ a ∷ᴸ a* ⟧ⱽ = Trees.con (just a) [ ⟦ a* ⟧ⱽ ]
\end{code}
\begin{code}[hide]
{-# TERMINATING #-}
\end{code}
The mapping of the syntax requires a few twists.
The $n$-ary $0$-function must be simulated by composing the corresponding $0$-ary tree constructor with an empty vector of $n$-ary functions.
Normal constructors, projection, and composition are as before.
The translation for primitive recursion merges the functions $g$ and $h$ into a single indexed function.
\begin{code}
⟦_⟧ : Words.PR A n → Trees.PR (make-R A) n
⟦ Words.Z ⟧      = Trees.C (Trees.σ nothing) []
⟦ Words.σ a ⟧    = Trees.σ (just a)
⟦ Words.π i ⟧    = Trees.π i
⟦ Words.C f g* ⟧ = Trees.C ⟦ f ⟧ (map ⟦_⟧ g*)
⟦ Words.P g h ⟧  = Trees.P λ{ nothing → ⟦ g ⟧ ; (just a) → ⟦ h a ⟧}
\end{code}
It is again straightforward to prove the soundness of this embedding.
\begin{code}
sound : ∀ (p : Words.PR A n) (v* : Vec (List A) n)
  → ⟦ Words.eval p v* ⟧ⱽ ≡ Trees.eval ⟦ p ⟧ (map ⟦_⟧ⱽ v*)
\end{code}
\begin{code}[hide]
sound* : ∀ (p* : Vec (Words.PR A n) m) (v* : Vec (List A) n)
  → map ⟦_⟧ⱽ (Words.eval* p* v*) ≡ Trees.eval* (map ⟦_⟧ p*) (map ⟦_⟧ⱽ v*)

sound Words.Z v* = refl
sound (Words.σ a) [ x ] = refl
sound (Words.π i) v* = sym (lookup-map i ⟦_⟧ⱽ v*)
sound (Words.C f g*) v* rewrite sound f (Words.eval* g* v*) | sound* g* v* = refl
sound (Words.P g h) ([]ᴸ ∷ v*) = sound g v*
sound (Words.P g h) ((x ∷ᴸ x₁) ∷ v*) = trans (sound (h x) (Words.eval (Words.P g h) (x₁ ∷ v*) ∷ x₁ ∷ v*))
                                            (cong (Trees.eval ⟦ h x ⟧)
                                                  (cong (_∷ ⟦ x₁ ⟧ⱽ ∷ map ⟦_⟧ⱽ v*)
                                                        (sound (Words.P g h) (x₁ ∷ v*))))

sound* [] v* = refl
sound* (p ∷ p*) v* rewrite sound p v* | sound* p* v* = refl
\end{code}
