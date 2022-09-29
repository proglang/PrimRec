{-# OPTIONS --rewriting --prop -v rewriting:50 #-}
{-# OPTIONS --allow-unsolved-metas #-}
module PRHVec where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _∸_; _+_)
open import Data.Vec using (Vec; []; _∷_; lookup; map)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Equality.Rewrite
open import Function using (id)

import System-T0 as T0 --using (Exp; evalST; evalSTClosed; ext2)

-- open System-T0.Exp
open import Utils
open import HVec
open import EvalPConstructor
import T0-SystemT-Embedding as T


data PR : ∀ {n : ℕ} -> T.Ctx n → T.Ty → Set where
        Z : ∀ {n : ℕ} {ctx : T.Ctx n} → PR ctx T.TyNat                                  -- zero
        σ : PR [ T.TyNat ] T.TyNat                                                      -- successor
        π : ∀ {n : ℕ} {ctx : T.Ctx n}{ty}(i : T.DBI ctx ty)                             -- i-th projection
            → PR ctx ty
        C : ∀ {n m : ℕ} {argsGS : T.Ctx n}{resGi : T.Ctx m}{tyF}(f : PR resGi tyF)      -- composition
            → (g* : HVec (λ t → PR argsGS t) resGi)
            → PR argsGS tyF
        P :  ∀ {n : ℕ} {argsG : T.Ctx n}{tyG} (g : PR argsG tyG)                        -- primitive recursion
            → (h : PR  (tyG ∷ (T.TyNat ∷ argsG)) tyG)
            → PR (T.TyNat ∷ argsG) tyG

eval* : ∀ {n m : ℕ} {ctx : T.Ctx n}{resGi : T.Ctx m} → HVec (PR ctx) resGi → HVec T.evalTy ctx →  HVec T.evalTy resGi

eval : ∀ {n : ℕ} {ctx : T.Ctx n}{ty} → PR ctx ty → HVec T.evalTy ctx → T.evalTy ty
eval Z hvs = 0
eval σ (x ∷ᴴ []ᴴ) = x + 1
eval (π i) hvs = lkupH i hvs
eval (C f g*) hvs = eval f (eval* g* hvs)
eval (P g h) (x ∷ᴴ hvs) = para  (λ acc' counter' → eval h (acc' ∷ᴴ (counter' ∷ᴴ hvs))) (eval g hvs) x 

eval* []ᴴ hs = []ᴴ
eval* (g ∷ᴴ gs) hs = eval g hs ∷ᴴ eval* gs hs

id≡id : ∀ {A : Set} (x : A)  →  id x ≡ x
id≡id x = refl


mapId : ∀ {A : Set} {n : ℕ} (xs : Vec A n) → map id xs ≡ xs
mapId [] = refl
mapId (x ∷ xs) rewrite mapId xs = refl 

{-# REWRITE  mapId #-}


eval*≡map-Eval :  ∀ {n m : ℕ} {ctx : T.Ctx n}{resGi : T.Ctx m} (gs : HVec (PR ctx) resGi) (hvs : HVec T.evalTy ctx) → eval*  gs hvs ≡ mapᴴ' {F = PR ctx }{G = T.evalTy}{tt = resGi}{res = id} (λ g → eval g hvs) gs
eval*≡map-Eval []ᴴ hvs = refl
eval*≡map-Eval (x ∷ᴴ gs) hvs = cong (λ v → eval x hvs ∷ᴴ v) (eval*≡map-Eval gs hvs)