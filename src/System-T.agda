{-# OPTIONS --rewriting --prop -v rewriting:50 #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _∸_)
open import Data.Vec using (Vec; []; _∷_; lookup; foldr;_++_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Equality.Rewrite
import System-T0 as T0 --using (Exp; evalST; evalSTClosed; ext2)

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



-- \end{code}
-- \newcommand{\prepLambdas}{%
-- \begin{code}
-- prepLambdas : ∀ {o} (n : ℕ) → (m : ℕ) →  Exp (m + n) o → Exp n (o + m)
-- prepLambdas {o} n zero exp   = exp
-- prepLambdas {o} n (suc m) exp   = Lam (prepLambdas  (suc n) m exp)


-- prepLambdasEval : ∀ {n m : ℕ} (ctx : Vec ℕ n ) (args : Vec ℕ m ) (exp : Exp (m + n) 0) → 
--         evalST (prepLambdas n m exp) ctx args ≡ evalST exp (args ++r ctx) []
-- prepLambdasEval ctx [] exp = refl
-- prepLambdasEval ctx (x ∷ args) exp = prepLambdasEval ((x ∷ ctx)) args  exp

-- prepLambdasEvalClose : ∀ {m : ℕ}  (args : Vec ℕ m ) (exp : Exp m zero) → 
--         evalSTClosed (prepLambdas 0 m exp) args ≡ evalST exp (fastReverse args) []
-- prepLambdasEvalClose = prepLambdasEval []
-- \end{code}}
-- \begin{code}[hide]