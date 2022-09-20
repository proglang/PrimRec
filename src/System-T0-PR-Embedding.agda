-- {-# OPTIONS --rewriting --prop -v rewriting:50 #-}
{-# OPTIONS --rewriting  #-}
{-# OPTIONS --allow-unsolved-metas #-}
module System-T0-PR-Embedding where



open import Data.Fin using (Fin; suc; zero; fromℕ; opposite; raise; inject+; inject₁; toℕ)
open import Data.Nat using (ℕ; suc; zero; _∸_; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; +-comm; +-assoc)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head; init; reverse; last; foldl) -- ; _ʳ++_) 
open import Data.Vec.Properties using (lookup-++ˡ; map-cong; lookup-++ʳ)
open import Function.Base using (const; _∘′_; id; _∘_; flip)
open import Data.Fin.Properties using (toℕ-fromℕ; fromℕ-toℕ) -- (++-assoc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂; _≗_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Equality.Rewrite
open import NatProperties using (assoc-comm-suc)
open import FinProperties using (inject+0; inject+1; inject+Add; inject+Eq)
open import VecProperties

open import System-T0 using (Exp; mkConstZero; mkProj; raiseExp0Eq; raiseExP; evalSTClosed; evalMkConstZero; evalMkProj; generalComp; evalGeneralComp; paraT; evalParaT; paraNat; para; paraNat'; cong3; extensionality; paraNatEq; evalST)
open System-T0.Exp

open import PR-Nat
open import Utils
open import HVec




sTtoPR : ∀ {n m} → Exp n m → PR (n + m)
sTtoPR (Var x) = π (opposite x)
sTtoPR (Lam exp) = sTtoPR exp
sTtoPR CZero = Z
sTtoPR {n}{m} Suc = C σ [ π (fromℕ n) ]
sTtoPR {n} (App f x) = {!   !}
sTtoPR (Nat n) = {!   !}
sTtoPR (PRecT h acc counter) = {!   !}


eqSTPRn : ∀  {n m : ℕ} ( exp : Exp n m) (ctx : Vec ℕ n ) (args : Vec ℕ m ) → eval (sTtoPR exp) (ctx ++r args) ≡ evalST exp ctx args
eqSTPRn (Var x) ctx [] = lookupOpRev x ctx
eqSTPRn (Lam exp) ctx (x ∷ args) = eqSTPRn exp (x ∷ ctx)(args)
eqSTPRn CZero ctx args = refl
eqSTPRn Suc ctx [ x ] = {!   !}
eqSTPRn (App exp exp₁) ctx args = {!   !}
eqSTPRn (Nat x) ctx [] = {!   !}
eqSTPRn (PRecT exp exp₁ exp₂) ctx [] = {!   !}

natToPR : ℕ → PR zero
natToPR zero = Z
natToPR (suc n) = C σ ( [ natToPR n ])

-- natToPRSound : ∀ {n: ℕ}