\begin{code}
module NatsVecToNats where

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; suc; zero; _*_; _+_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head; zipWith)
open import Data.Vec.Properties using (lookup-map)
open import Data.List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_; _++_ to _++ᴸ_; length to lengthᴸ; map to mapᴸ)
open import Function using (_∘_)

open import Utils

import PR-Nat as Nats
import PR-NatsVec as NatsVec

----------------------------------------------------------------------
-- proposition:
-- a vector-valued PR function computes a single-valued pr function in every component
-- not clear how to handle the pr case
----------------------------------------------------------------------

⟦_⟧ : NatsVec.PR m n → Vec (Nats.PR m) n
⟦ NatsVec.`0 ⟧ = []
⟦ NatsVec.Z ⟧ = [ Nats.Z ]
⟦ NatsVec.σ ⟧ = [ Nats.σ ]
⟦ NatsVec.π i ⟧ = [ Nats.π i ]
⟦ NatsVec.C f g ⟧ = map (λ f′ → Nats.C f′ ⟦ g ⟧) ⟦ f ⟧
⟦ NatsVec.♯ f g ⟧ = ⟦ f ⟧ ++ ⟦ g ⟧
⟦ NatsVec.P g h ⟧ = zipWith (λ g′ h′ → Nats.P g′ (Nats.C h′ {!!})) ⟦ g ⟧ ⟦ h ⟧
-- map (λ g′ → Nats.P g′ {!!}) ⟦ g ⟧


\end{code}
