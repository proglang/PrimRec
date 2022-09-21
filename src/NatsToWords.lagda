\begin{code}[hide]
module NatsToWords where

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

import PR-Nat as Nats
import PR-Words as Words

-- pr on words simulates pr on natural numbers

{-# TERMINATING #-}
\end{code}
\begin{code}
⟦_⟧ : Nats.PR n → Words.PR ⊤ n
⟦ Nats.Z ⟧      = Words.Z
⟦ Nats.σ ⟧      = Words.σ tt
⟦ Nats.π i ⟧    = Words.π i
⟦ Nats.C f g* ⟧ = Words.C ⟦ f ⟧ (map ⟦_⟧ g*)
⟦ Nats.P g h ⟧  = Words.P ⟦ g ⟧ (λ{ tt → ⟦ h ⟧})
\end{code}
To state soundness of the embedding, we need the embedding
\begin{code}[inline]
⟦_⟧ⱽ : ℕ → List ⊤
\end{code}
which we extend to vectors in the natural way.
\begin{code}[hide]
⟦ zero ⟧ⱽ  = []ᴸ
⟦ suc n ⟧ⱽ = tt ∷ᴸ ⟦ n ⟧ⱽ
\end{code}
\begin{code}
sound : ∀ (p : Nats.PR n) (v* : Vec ℕ n)
  → ⟦ Nats.eval p v* ⟧ⱽ ≡ Words.eval ⟦ p ⟧ (map ⟦_⟧ⱽ v*)
\end{code}
The proof is by induction on the program \AgdaBound{p}.
\begin{code}[hide]
sound* : ∀ {m} p* (v* : Vec ℕ n)
  → map{n = m} ⟦_⟧ⱽ (Nats.eval* p* v*) ≡ Words.eval* (map ⟦_⟧ p*) (map ⟦_⟧ⱽ v*)

sound Nats.Z v* = refl
sound Nats.σ [ x ] = refl
sound (Nats.π i) v* = sym (lookup-map i ⟦_⟧ⱽ v*)
sound (Nats.C f g*) v* rewrite sound f (Nats.eval* g* v*) | sound* g* v* = refl
sound (Nats.P g h) (zero ∷ v*) = sound g v*
sound (Nats.P g h) (suc x ∷ v*) = trans (sound h (Nats.eval (Nats.P g h) (x ∷ v*) ∷ x ∷ v*))
                                        (cong (Words.eval ⟦ h ⟧) 
                                              (cong (_∷ ⟦ x ⟧ⱽ ∷ map ⟦_⟧ⱽ v*)
                                                    (sound (Nats.P g h) (x ∷ v*))))

sound* [] v* = refl
sound* (p ∷ p*) v* rewrite sound p v* | sound* p* v* = refl
\end{code}
\begin{code}[hide]
-- here we can also prove the reverse direction

{-# TERMINATING #-}
⟦_⟧ᴿ : Words.PR ⊤ n → Nats.PR n
⟦ Words.Z ⟧ᴿ = Nats.Z
⟦ Words.σ tt ⟧ᴿ = Nats.σ
⟦ Words.π i ⟧ᴿ = Nats.π i
⟦ Words.C p g* ⟧ᴿ = Nats.C ⟦ p ⟧ᴿ (map ⟦_⟧ᴿ g*)
⟦ Words.P p h ⟧ᴿ = Nats.P ⟦ p ⟧ᴿ ⟦ h tt ⟧ᴿ

⟦_⟧ᴿⱽ : List ⊤ → ℕ
⟦ []ᴸ ⟧ᴿⱽ = zero
⟦ tt ∷ᴸ xs ⟧ᴿⱽ = suc ⟦ xs ⟧ᴿⱽ

{-# TERMINATING #-}
soundᴿ : ∀ p (v* : Vec (List ⊤) n)
  → ⟦ Words.eval p v* ⟧ᴿⱽ ≡ Nats.eval ⟦ p ⟧ᴿ (map ⟦_⟧ᴿⱽ v*)
soundᴿ* : ∀ {m} p* (v* : Vec (List ⊤) n)
  → map{n = m} ⟦_⟧ᴿⱽ (Words.eval* p* v*) ≡ Nats.eval* (map ⟦_⟧ᴿ p*) (map ⟦_⟧ᴿⱽ v*)

soundᴿ Words.Z v* = refl
soundᴿ (Words.σ a) [ v ] = refl
soundᴿ (Words.π i) v* = sym (lookup-map i ⟦_⟧ᴿⱽ v*)
soundᴿ (Words.C f g*) v* rewrite soundᴿ f (Words.eval* g* v*) | soundᴿ* g* v* = refl
soundᴿ (Words.P p h) ([]ᴸ ∷ v*) = soundᴿ p v*
soundᴿ (Words.P p h) ((tt ∷ᴸ xs) ∷ v*)
  rewrite soundᴿ (h tt) (Words.eval (Words.P p h) (xs ∷ v*) ∷ xs ∷ v*)
        | soundᴿ (Words.P p h) (xs ∷ v*) = refl

soundᴿ* [] v* = refl
soundᴿ* (p ∷ p*) v* rewrite soundᴿ p v* | soundᴿ* p* v* = refl
\end{code}


