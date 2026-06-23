
{-# OPTIONS --rewriting --prop -v rewriting:50 #-}


module System-T-PR-HVec-Embedding where





open import Data.Fin using (Fin; suc; zero; opposite; fromℕ; _↑ˡ_)
open import Data.Nat using (ℕ; suc; zero; _∸_; _+_)
open import Data.Nat.Properties using (+-comm)

open import Data.Vec using (Vec; []; _∷_; lookup; foldr;_++_; map)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂; subst)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Agda.Builtin.Equality.Rewrite
-- import System-T0 as T0 --using (Exp; evalST; evalSTClosed; ext2)

-- open System-T0.Exp
open import Utils
open import HVec
open import EvalPConstructor using (para)
open import VecProperties
open import FinProperties

open import System-T using (Ctx; Ty; getArgs; Exp; countArgs)
open Ty
open Exp
open import PRHVec
open import System-T0-PR-Embedding using (toN; mToM+N; zeroToM-Inject+N; helperLookupMapRaise; helperLookupMapInject; mapToNRaiseEq; mapToNInjectEq; lookupToN=id)
-- {-# REWRITE inject+0 #-}


helper : ∀ {n : ℕ} (ctx : Ctx n)  → lookup (ctx ++r getArgs (TyNat ⇒ TyNat)) (fromℕ n) ≡ TyNat
helper ctx = lkupfromN ctx []

-- lookupToN=id
 -- mapToNInjectEq mapToNRaiseEq helperLookupMapInject

-- {-# REWRITE  #-}
helper2 : ∀ {n : ℕ}(tyA tyB : Ty) (ctx : Ctx n) → (reverse ctx ++ tyA ∷ getArgs tyB) ≡ (ctx ++r getArgs (tyA ⇒ tyB))
helper2 {_}  tyA tyB ctx = sym (++r=reverse++ ctx (tyA ∷ (getArgs tyB)) )

helper3 :  ∀ {n m : ℕ}(ctx : Ctx (n)) → (fins : Vec (Fin (n )) m) → HVec (PR (ctx)) (map (λ f → lookup  (ctx) f) fins )
helper3 ctx  [] = []ᴴ
helper3 {n} {m} (ctx) (f ∷ fins) = (π f) ∷ᴴ helper3 ctx  fins


helper4 : ∀ {n : ℕ} (ctx : Ctx n) (f : Fin n) → (map (lookup (reverse ctx ++ getArgs (lookup ctx f))) (zeroToM-Inject+N (countArgs (lookup ctx f)) n)) ≡ reverse ctx
helper4 ctx f = mapToNInjectEq (reverse ctx) (getArgs (lookup ctx f))


helper5 : ∀ {n : ℕ} (ctx : Ctx n)(tyB) → map (lookup (reverse ctx ++ getArgs tyB)) (map (λ i → i ↑ˡ countArgs tyB) (toN n)) ≡ reverse ctx
helper5 ctx tyB = mapToNInjectEq (reverse ctx) (getArgs tyB)



{-# REWRITE helper mapToNInjectEq mapToNRaiseEq   lookupToN=id   #-}


postulate
  embedd-ST-PR : ∀ {n : ℕ} {ctx : Ctx n} {ty : Ty}
    → Exp ctx ty → PR (ctx ++r getArgs ty) TyNat
