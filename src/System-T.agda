{-# OPTIONS --rewriting  #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Fin using (Fin; suc; zero; opposite)
open import Data.Nat using (ℕ; suc; zero; _∸_; _+_)
open import Data.Vec using (Vec; []; _∷_; lookup; foldr;_++_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Equality.Rewrite
-- import System-T0 as T0 --using (Exp; evalST; evalSTClosed; ext2)

-- open System-T0.Exp
open import PR-Nat
open import Utils
open import HVec
open import EvalPConstructor using (para)
open import VecProperties


data Ty : Set where
    TyNat : Ty
    _⇒_ : Ty → Ty → Ty


Ctx : ℕ → Set 
Ctx n  = Vec (Ty) n


-- DBI : ∀ {n : ℕ} -> Ctx n  -> Ty -> Set
-- DBI = HIndex


-- data DBI : ∀ {n : ℕ} -> Ctx n  -> Ty -> Set where
--     ZDB : ∀ {n : ℕ} {ts : Ctx n}  {t} → DBI (t ∷ ts) t
--     SDB : ∀ {n : ℕ} {ts : Ctx n} {t t' : Ty} → DBI (ts) t → DBI (t' ∷ ts) t

data Exp : ∀ {n : ℕ} -> Ctx n  -> Ty -> Set where
    Var : ∀ {n : ℕ} {ctx : Ctx n}  → (f : Fin n) → Exp ctx (lookup ctx f)
    Lam  : ∀ {n : ℕ} {ctx : Ctx n} { tyA tyB} → Exp (tyA ∷ ctx) tyB → Exp ctx  (tyA ⇒ tyB)
    CZero :   ∀ {n : ℕ} {ctx : Ctx n} → Exp ctx TyNat
    Suc : ∀ {n : ℕ} {ctx : Ctx n} → Exp ctx (TyNat ⇒ TyNat)
    App : ∀ {n : ℕ} {ctx : Ctx n} {tyA tyB} →   Exp ctx (tyA ⇒ tyB) → Exp ctx tyA → Exp ctx tyB
    Nat : ∀ {n : ℕ} {ctx : Ctx n} → ℕ → Exp ctx TyNat
    PrecT : ∀ {n : ℕ} {ctx : Ctx n}{ty} → Exp ctx (ty ⇒ (TyNat ⇒ ty)) → Exp ctx (ty) → Exp ctx (TyNat) → Exp ctx (ty)




evalTy : Ty → Set
evalTy TyNat = ℕ
evalTy (tyA ⇒ tyB) = (evalTy tyA) → (evalTy tyB)

evalExp : ∀ {n : ℕ} {ctx : Ctx n} {ty : Ty}  → Exp ctx ty → HVec evalTy ctx → (evalTy ty)
evalExp (Var x) ctx = hlookup  ctx x -- hlookup x ctx
evalExp (Lam exp) ctx = λ x → evalExp exp (x ∷ᴴ ctx)
evalExp CZero ctx = 0
evalExp Suc ctx = λ x → suc x
evalExp (App f x) ctx = (evalExp f ctx) (evalExp x ctx)
evalExp (Nat n) ctx = n
evalExp (PrecT h acc counter) ctx = para (evalExp h ctx) (evalExp acc ctx) (evalExp counter ctx)



-- -- ------------------------------------------------------------------------------
-- -- -- uncurryH
-- -- ------------------------------------------------------------------------------


countArgs : Ty → ℕ
countArgs TyNat = 0
countArgs (tyA ⇒ tyB) = suc (countArgs tyB)

getArgs : (ty : Ty) -> Vec Ty (countArgs ty) 
getArgs TyNat = []
getArgs (ty ⇒ tyB) = ty ∷ getArgs tyB

-- init' : ∀  {n : ℕ} {A : Set} → Vec A n → Vec A (n ∸ 1 )
-- init' [] = []
-- init' [ x ] = []
-- init' (x ∷ y ∷ vs) = x ∷ init' (y ∷ vs)

uncurryH : ∀ {ty : Ty} → evalTy ty → HVec evalTy ( (getArgs ty))  → ℕ
uncurryH {TyNat} exp hxs = exp
uncurryH {tyA ⇒ tyB} f (x ∷ᴴ hxs) = uncurryH (f x) hxs



evalExp' : ∀ {n : ℕ} {ctx : Ctx n} {ty : Ty}  → Exp ctx ty → HVec evalTy ctx → HVec evalTy (getArgs ty) → ℕ
evalExp' exp ctx = uncurryH (evalExp exp ctx)



------------------------------------------------------------------------------
-- helper
------------------------------------------------------------------------------

prepArgs : ∀ {n : ℕ} → Ctx n → Ty → Ty
prepArgs ctx ty = foldr (λ x → Ty) (λ x acc → x ⇒ acc) ty ctx

prepLambdas : ∀ {m n}{ty} (xs :  Ctx n) (ys : Ctx m) →  Exp (ys ++r xs) ty → Exp xs (prepArgs ys ty)
prepLambdas xs [] exp = exp
prepLambdas xs (x ∷ ys) exp = Lam (prepLambdas (x ∷ xs) ys exp)



helper3 : ∀ (n : ℕ) (ty : Ty)(xs : Vec Ty n ) → countArgs (foldr (λ x → Ty) _⇒_ ty xs)  ≡ n + countArgs ty 
helper3 _ _ [] = refl
helper3 (suc n) ty (x ∷ xs) = cong suc (helper3 n ty xs)

{-# REWRITE helper3 #-}

helper2 : ∀ {n : ℕ} {ty : Ty} (xs : Vec Ty n ) →  (getArgs (prepArgs xs ty)) ≡ xs ++ getArgs ty
helper2 [] = refl
helper2 (x ∷ xs) = cong (λ v → x ∷ v) (helper2 xs)

{-# REWRITE helper2 #-}


prepLambdasEval : ∀ {n m : ℕ} {ty : Ty} (xs : Vec Ty n ) (ys : Vec Ty m ) (exp : Exp (xs ++r ys) ty) (xs' : HVec evalTy xs ) (ys' : HVec evalTy ys) (args : HVec evalTy (getArgs ty)) → 
             evalExp' (prepLambdas ys xs exp) ys' (xs' ++ᴴ   args)  ≡ evalExp' exp (xs' ++rᴴ ys') args
prepLambdasEval .[] ys exp []ᴴ ys' args = refl
prepLambdasEval (x ∷ xs) ys exp (x' ∷ᴴ xs') ys' args rewrite prepLambdasEval xs (x ∷ ys) exp xs' (x' ∷ᴴ ys') args = refl

prepLambdasEvalClose : ∀ {n : ℕ} {ty : Ty} (xs : Vec Ty n )  (exp : Exp (xs ++r []) ty) (xs' : HVec evalTy xs )  (args : HVec evalTy (getArgs ty)) → 
             evalExp' (prepLambdas [] xs exp) []ᴴ (xs' ++ᴴ   args)  ≡ evalExp' exp (xs' ++rᴴ []ᴴ) args
prepLambdasEvalClose xs exp xs' args = prepLambdasEval xs [] exp xs' []ᴴ args


------------------------------------------------------------------------------
-- constant zero-function
------------------------------

mkConstZero :  ∀ {n  : ℕ}  (xs : Vec Ty n ) → Exp [] (prepArgs xs TyNat) 
mkConstZero xs = prepLambdas [] xs CZero

{-# REWRITE  ++identityRᴴ #-}


evalMkConstZero : ∀ {n  : ℕ}  (xs : Vec Ty n ) (xs' : HVec evalTy xs) → evalExp' (mkConstZero xs)  []ᴴ  xs'  ≡ 0
evalMkConstZero xs xs'  rewrite ++identityRᴴ xs' = prepLambdasEvalClose xs CZero xs' []ᴴ

------------------------------------------------------------------------------
-- projection
------------------------------------------------------------------------------
{-# REWRITE  lookupOpRev #-}

mkProj : ∀ {n  : ℕ}  (xs : Vec Ty n ) → (f : Fin n)  →  Exp [] (prepArgs (xs) (lookup (xs) ( f))) 
mkProj xs f = prepLambdas [] ( xs)  (Var (opposite f))

evalMkProj : ∀ {n  : ℕ}  {xs : Vec Ty n }  (f : Fin n) (xs' : HVec evalTy xs)   → 
        evalExp' (mkProj xs f)  []ᴴ (xs' ++ᴴ {!   !})  ≡  {!   !} -- hlookup xs' f
evalMkProj i vs = {!   !} -- evalST (mkProj i) [] vs 
--     ≡⟨ prepLambdasEvalClose vs (Var (opposite i)) ⟩ 
--                         lookup (vs ᴿ) (opposite i) 
--     ≡⟨ lookupOpRev i vs ⟩ 
--                         lookup vs i
--     ∎ 
