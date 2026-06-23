\begin{code}
module NatsVecToNats where

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
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
import PR-Nat-Example as NatsExample
import PR-NatsVec as NatsVec

----------------------------------------------------------------------
-- proposition:
-- a vector-valued PR function computes a single-valued pr function in every component
-- not clear how to handle the pr case
----------------------------------------------------------------------
helper : Vec (Nats.PR m) 1 → Vec (Nats.PR (suc (suc m))) 1 → Vec (Nats.PR ((suc m))) 1
helper g h = [ Nats.P (head g) (head h) ]  -- [ Nats.P g h ]

encode : Vec (Nats.PR m) n → Nats.PR m
encode [] = Nats.C Nats.Z []
encode (f ∷ fs) = Nats.C NatsExample.mkpairP [ f , encode fs ]

decode : ∀ n → Nats.PR m → Vec (Nats.PR m) n
decode zero f = []
decode (suc n) f =
  Nats.C NatsExample.unpair-xP [ f ] ∷
  decode n (Nats.C NatsExample.unpair-yP [ f ])

tail-projections : ∀ m → Vec (Nats.PR (suc (suc m))) (suc m)
tail-projections m = map Nats.π (map suc (Nats.allFin (suc m)))

compile-P-step : ∀ {m n}
  → Vec (Nats.PR (n + suc m)) n
  → Nats.PR (suc (suc m))
compile-P-step {m} {n} h =
  encode (map (λ f → Nats.C f
    (decode n (Nats.π zero) ++ tail-projections m)) h)

compile-P : ∀ {m n}
  → Vec (Nats.PR m) n
  → Vec (Nats.PR (n + suc m)) n
  → Vec (Nats.PR (suc m)) n
compile-P {n = n} g h = decode n (Nats.P (encode g) (compile-P-step h))

⟦_⟧ : NatsVec.PR m n → Vec (Nats.PR m) n
⟦ NatsVec.`0 ⟧ = []
⟦ NatsVec.Z ⟧ = [ Nats.Z ]
⟦ NatsVec.σ ⟧ = [ Nats.σ ]
⟦ NatsVec.π i ⟧ = [ Nats.π i ]
⟦ NatsVec.C f g ⟧ = map (λ f′ → Nats.C f′ ⟦ g ⟧) ⟦ f ⟧
⟦ NatsVec.♯ f g ⟧ = ⟦ f ⟧ ++ ⟦ g ⟧
⟦ NatsVec.P g h ⟧ = compile-P ⟦ g ⟧ ⟦ h ⟧
⟦ NatsVec.P' g h ⟧ = helper ⟦ g ⟧ ⟦ h ⟧ 

\end{code}

\begin{code}[hide]

sound-natVecToNats-Helper  : ∀  {m n o} →  (g : Vec (Nats.PR o ) n) (h : Vec (Nats.PR m ) o ) ( args : Vec ℕ m) → 
      Nats.eval* (map (λ f′ → Nats.C f′ h) g) args ≡
      Nats.eval* g (Nats.eval* h args)
sound-natVecToNats-Helper [] h args = refl
sound-natVecToNats-Helper (g ∷ gs) h args = cong (λ v → Nats.eval g (Nats.eval* h args) ∷ v) (sound-natVecToNats-Helper gs h args)

helper-PR-Z : ∀ (g : NatsVec.PR n 1) (h : NatsVec.PR (2 + n ) 1 ) (args : Vec ℕ ( n)) → Nats.eval* (⟦ NatsVec.P' g h ⟧ ) (0 ∷ args) ≡
      Nats.eval* ⟦ g ⟧ args
helper-PR-Z g h args  with ⟦ g ⟧  
... | [ g' ] = refl

sound-natVecToNats : ∀ {n m} (prs : NatsVec.PR m n) (args : Vec ℕ m) → Nats.eval* (⟦ prs ⟧) args  ≡ NatsVec.eval prs args

encode-value : Vec ℕ n → ℕ
encode-value [] = 0
encode-value (x ∷ xs) = NatsExample.mkpair x (encode-value xs)

decode-value : ∀ n → ℕ → Vec ℕ n
decode-value zero p = []
decode-value (suc n) p =
  NatsExample.unpair-x p ∷ decode-value n (NatsExample.unpair-y p)

decode-encode-value : ∀ (xs : Vec ℕ n) →
  decode-value n (encode-value xs) ≡ xs
decode-encode-value [] = refl
decode-encode-value (x ∷ xs)
  rewrite NatsExample.unpair-pair-identity-x x (encode-value xs)
        | NatsExample.unpair-pair-identity-y x (encode-value xs)
        | decode-encode-value xs = refl

eval-encode : ∀ (fs : Vec (Nats.PR m) n) (args : Vec ℕ m) →
  Nats.eval (encode fs) args ≡ encode-value (Nats.eval* fs args)
eval-encode [] args = refl
eval-encode (f ∷ fs) args
  rewrite NatsExample.mkpairP=mkpair
    (Nats.eval f args) (Nats.eval (encode fs) args)
        | eval-encode fs args = refl

eval-decode : ∀ n (f : Nats.PR m) (args : Vec ℕ m) →
  Nats.eval* (decode n f) args ≡ decode-value n (Nats.eval f args)
eval-decode zero f args = refl
eval-decode (suc n) f args
  rewrite NatsExample.unpair-xP=unpair-x (Nats.eval f args)
        | eval-decode n (Nats.C NatsExample.unpair-yP [ f ]) args
        | NatsExample.unpair-yP=unpair-y (Nats.eval f args) = refl

eval*-++ : ∀ (fs : Vec (Nats.PR m) n) (gs : Vec (Nats.PR m) o)
  (args : Vec ℕ m) →
  Nats.eval* (fs ++ gs) args ≡ Nats.eval* fs args ++ Nats.eval* gs args
eval*-++ [] gs args = refl
eval*-++ (f ∷ fs) gs args rewrite eval*-++ fs gs args = refl

eval-tail-projections : ∀ m (acc counter : ℕ) (args : Vec ℕ m) →
  Nats.eval* (tail-projections m) (acc ∷ counter ∷ args) ≡ counter ∷ args
eval-tail-projections m acc counter args
  rewrite Nats.eval*-projections (map suc (Nats.allFin (suc m)))
    (acc ∷ counter ∷ args)
        | ∘-map (lookup (acc ∷ counter ∷ args)) suc (Nats.allFin (suc m))
        | Nats.lookup-allFin (counter ∷ args) = refl

eval-compile-P-inputs : ∀ {m n} (xs : Vec ℕ n) (counter : ℕ)
  (args : Vec ℕ m) →
  Nats.eval* (decode n (Nats.π zero) ++ tail-projections m)
    (encode-value xs ∷ counter ∷ args) ≡ xs ++ counter ∷ args
eval-compile-P-inputs {m} {n} xs counter args
  rewrite eval*-++ (decode n (Nats.π zero)) (tail-projections m)
    (encode-value xs ∷ counter ∷ args)
        | eval-decode n (Nats.π zero) (encode-value xs ∷ counter ∷ args)
        | decode-encode-value xs
        | eval-tail-projections m (encode-value xs) counter args = refl

eval-compile-P-step : ∀ {m n}
  (h : Vec (Nats.PR (n + suc m)) n) (xs : Vec ℕ n)
  (counter : ℕ) (args : Vec ℕ m) →
  Nats.eval (compile-P-step h) (encode-value xs ∷ counter ∷ args) ≡
  encode-value (Nats.eval* h (xs ++ counter ∷ args))
eval-compile-P-step {m} {n} h xs counter args =
  begin
    Nats.eval (compile-P-step h) (encode-value xs ∷ counter ∷ args)
  ≡⟨ eval-encode
       (map (λ f → Nats.C f
         (decode n (Nats.π zero) ++ tail-projections m)) h)
       (encode-value xs ∷ counter ∷ args) ⟩
    encode-value
      (Nats.eval*
        (map (λ f → Nats.C f
          (decode n (Nats.π zero) ++ tail-projections m)) h)
        (encode-value xs ∷ counter ∷ args))
  ≡⟨ cong encode-value
       (sound-natVecToNats-Helper h
         (decode n (Nats.π zero) ++ tail-projections m)
         (encode-value xs ∷ counter ∷ args)) ⟩
    encode-value
      (Nats.eval* h
        (Nats.eval* (decode n (Nats.π zero) ++ tail-projections m)
          (encode-value xs ∷ counter ∷ args)))
  ≡⟨ cong (encode-value ∘ Nats.eval* h)
       (eval-compile-P-inputs xs counter args) ⟩
    encode-value (Nats.eval* h (xs ++ counter ∷ args))
  ∎

sound-compile-P-scalar : ∀ {m n} (x : ℕ) (args : Vec ℕ m)
  (g : NatsVec.PR m n) (h : NatsVec.PR (n + suc m) n) →
  Nats.eval (Nats.P (encode ⟦ g ⟧) (compile-P-step ⟦ h ⟧)) (x ∷ args) ≡
  encode-value (NatsVec.eval (NatsVec.P g h) (x ∷ args))
sound-compile-P-scalar zero args g h =
  trans (eval-encode ⟦ g ⟧ args)
        (cong encode-value (sound-natVecToNats g args))
sound-compile-P-scalar (suc x) args g h =
  begin
    Nats.eval (Nats.P (encode ⟦ g ⟧) (compile-P-step ⟦ h ⟧))
      (suc x ∷ args)
  ≡⟨⟩
    Nats.eval (compile-P-step ⟦ h ⟧)
      (Nats.eval (Nats.P (encode ⟦ g ⟧) (compile-P-step ⟦ h ⟧))
        (x ∷ args) ∷ x ∷ args)
  ≡⟨ cong (λ acc → Nats.eval (compile-P-step ⟦ h ⟧)
       (acc ∷ x ∷ args)) (sound-compile-P-scalar x args g h) ⟩
    Nats.eval (compile-P-step ⟦ h ⟧)
      (encode-value (NatsVec.eval (NatsVec.P g h) (x ∷ args)) ∷ x ∷ args)
  ≡⟨ eval-compile-P-step ⟦ h ⟧
       (NatsVec.eval (NatsVec.P g h) (x ∷ args)) x args ⟩
    encode-value
      (Nats.eval* ⟦ h ⟧
        (NatsVec.eval (NatsVec.P g h) (x ∷ args) ++ x ∷ args))
  ≡⟨ cong encode-value
       (sound-natVecToNats h
         (NatsVec.eval (NatsVec.P g h) (x ∷ args) ++ x ∷ args)) ⟩
    encode-value
      (NatsVec.eval h
        (NatsVec.eval (NatsVec.P g h) (x ∷ args) ++ x ∷ args))
  ≡⟨⟩
    encode-value (NatsVec.eval (NatsVec.P g h) (suc x ∷ args))
  ∎

sound-general-P : ∀ {m n} (g : NatsVec.PR m n)
  (h : NatsVec.PR (n + suc m) n) (args : Vec ℕ (suc m)) →
  Nats.eval* (compile-P ⟦ g ⟧ ⟦ h ⟧) args ≡ NatsVec.eval (NatsVec.P g h) args
sound-general-P {n = n} g h (x ∷ args) =
  begin
    Nats.eval* (compile-P ⟦ g ⟧ ⟦ h ⟧) (x ∷ args)
  ≡⟨ eval-decode n
       (Nats.P (encode ⟦ g ⟧) (compile-P-step ⟦ h ⟧)) (x ∷ args) ⟩
    decode-value n
      (Nats.eval (Nats.P (encode ⟦ g ⟧) (compile-P-step ⟦ h ⟧))
        (x ∷ args))
  ≡⟨ cong (decode-value n) (sound-compile-P-scalar x args g h) ⟩
    decode-value n (encode-value (NatsVec.eval (NatsVec.P g h) (x ∷ args)))
  ≡⟨ decode-encode-value (NatsVec.eval (NatsVec.P g h) (x ∷ args)) ⟩
    NatsVec.eval (NatsVec.P g h) (x ∷ args)
  ∎


sound-P : ∀ (x : ℕ)(args  : Vec ℕ m)(g : NatsVec.PR m 1) (h : NatsVec.PR (suc (suc m)) 1) → 
  Nats.eval* (helper ⟦ g ⟧ ⟦ h ⟧) (x ∷ args) ≡ NatsVec.eval (NatsVec.P' g h) (x ∷ args)
sound-P zero args g h rewrite sym( sound-natVecToNats g args) = helper-PR-Z g h args
sound-P (suc x) args g h 
  rewrite  sym (sound-natVecToNats h (NatsVec.eval (NatsVec.P' g h) (x ∷ args) ++ x ∷ args) ) 
  | sym (sound-P x args g h)  with ⟦ h ⟧
... | [ h' ] 

  = cong (_∷ []) (cong (Nats.eval h')  refl )

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
sound-natVecToNats (NatsVec.P g h) args = sound-general-P g h args
sound-natVecToNats (NatsVec.P' g h) (x ∷ args) =   sound-P x args g h
\end{code}
