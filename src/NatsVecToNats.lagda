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
helper : Vec (Nats.PR m) 1 → Vec (Nats.PR (suc (suc m))) 1 → Vec (Nats.PR ((suc m))) 1
helper [ g ] [ h ] = [ Nats.P g h ]

⟦_⟧ : NatsVec.PR m n → Vec (Nats.PR m) n
⟦ NatsVec.`0 ⟧ = []
⟦ NatsVec.Z ⟧ = [ Nats.Z ]
⟦ NatsVec.σ ⟧ = [ Nats.σ ]
⟦ NatsVec.π i ⟧ = [ Nats.π i ]
⟦ NatsVec.C f g ⟧ = map (λ f′ → Nats.C f′ ⟦ g ⟧) ⟦ f ⟧
⟦ NatsVec.♯ f g ⟧ = ⟦ f ⟧ ++ ⟦ g ⟧
-- ⟦ NatsVec.P g h ⟧ = zipWith (λ g′ h′ → Nats.P g′ (Nats.C h′ {!!})) ⟦ g ⟧ ⟦ h ⟧
-- -- map (λ g′ → Nats.P g′ {!!}) ⟦ g ⟧
⟦ NatsVec.P g h ⟧ = zipWith (λ g' h' → Nats.P g' (Nats.C h' {!   !}))⟦ g ⟧ ⟦ h ⟧ 
⟦ NatsVec.P' g h ⟧ = helper ⟦ g ⟧ ⟦ h ⟧ 

-- with ⟦ g ⟧ 
-- ... | [ g' ] with ⟦ h ⟧ 
-- ... | [ h' ] =  [ Nats.P g' h' ]
\end{code}

\begin{code}[hide]

sound-natVecToNats-Helper  : ∀  {m n o} →  (g : Vec (Nats.PR o ) n) (h : Vec (Nats.PR m ) o ) ( args : Vec ℕ m) → 
      Nats.eval* (map (λ f′ → Nats.C f′ h) g) args ≡
      Nats.eval* g (Nats.eval* h args)
sound-natVecToNats-Helper [] h args = refl
sound-natVecToNats-Helper (g ∷ gs) h args = cong (λ v → Nats.eval g (Nats.eval* h args) ∷ v) (sound-natVecToNats-Helper gs h args)

helper-PR-Z : ∀ (g : NatsVec.PR n 1) (h : NatsVec.PR (2 + n ) 1 ) (args : Vec ℕ ( n)) → Nats.eval* (⟦ NatsVec.P' g h ⟧ ) (0 ∷ args) ≡
      Nats.eval* ⟦ g ⟧ args
helper-PR-Z g h args with ⟦ g ⟧  
... | [ g' ] with ⟦ h ⟧ 
... | [ h' ] = refl


sound-natVecToNats : ∀ {n m} (prs : NatsVec.PR m n) (args : Vec ℕ m) → Nats.eval* (⟦ prs ⟧) args  ≡ NatsVec.eval prs args

sound-P-Helper : ∀ (x : ℕ)(args  : Vec ℕ m)(g : Vec (Nats.PR m) 1) (h : Vec (Nats.PR (suc (suc m))) 1) → 
  Nats.eval* (helper g h ) (suc x ∷ args) ≡
      Nats.eval* h
      (Nats.eval* (helper  g  h) (x ∷ args) ++ x ∷ args)
sound-P-Helper x args [ g' ] [ h' ] = cong (λ x → [ x ]) refl

sound-P : ∀ (x : ℕ)(args  : Vec ℕ m)(g : NatsVec.PR m 1) (h : NatsVec.PR (suc (suc m)) 1) → 
  Nats.eval* (helper ⟦ g ⟧ ⟦ h ⟧) (x ∷ args) ≡ NatsVec.eval (NatsVec.P' g h) (x ∷ args)
sound-P zero args g h rewrite sym( sound-natVecToNats g args) = helper-PR-Z g h args
sound-P (suc x) args g h rewrite sym (sound-natVecToNats h (NatsVec.eval (NatsVec.P' g h) (x ∷ args) ++ x ∷ args) ) | 
  sym (sound-natVecToNats ((NatsVec.P' g h)) ((x ∷ args))) = sound-P-Helper x args ⟦ g ⟧ ⟦ h ⟧ 

sound-natVecToNats NatsVec.`0 args = refl
sound-natVecToNats NatsVec.Z [] = refl
sound-natVecToNats NatsVec.σ [ x ] = refl
sound-natVecToNats (NatsVec.π i) args = refl
sound-natVecToNats (NatsVec.C g h) args  rewrite sym (sound-natVecToNats h args) | sym (sound-natVecToNats g (Nats.eval* ⟦ h ⟧ args) ) = sound-natVecToNats-Helper ⟦ g ⟧  ⟦ h ⟧  args
sound-natVecToNats (NatsVec.♯ g h) args rewrite 
  sym (sound-natVecToNats h args) | 
  sym(sound-natVecToNats g args) | 
  Nats.eval*≡map-eval  ⟦ g ⟧ args | 
  Nats.eval*≡map-eval  ⟦ h ⟧ args |
  Nats.eval*≡map-eval  (⟦ g ⟧ ++ ⟦ h ⟧) args |
  ++-map (λ p → Nats.eval p args) ⟦ g ⟧ ⟦ h ⟧ = refl
sound-natVecToNats (NatsVec.P g h) (zero ∷ args) rewrite sym( sound-natVecToNats g args) = {!   !}
sound-natVecToNats (NatsVec.P prs prs₁) (suc x ∷ args) = {!   !}
sound-natVecToNats (NatsVec.P' g h) (x ∷ args) =   sound-P x args g h






\end{code} 