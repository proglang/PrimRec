{-# OPTIONS --rewriting  #-}

open import Data.Fin using (Fin; suc; zero; opposite; fromℕ; _↑ˡ_)
open import Data.Nat using (ℕ; suc; zero; _∸_; _+_)
open import Data.Vec using (Vec; []; _∷_; lookup; foldr;_++_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans; cong₂)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Agda.Builtin.Equality.Rewrite

open import Utils
open import HVec
open import EvalPConstructor using (para)
open import VecProperties
open import FinProperties using (inject+0)


data Ty : Set where
    TyNat : Ty
    _⇒_ : Ty → Ty → Ty


Ctx : ℕ → Set 
Ctx n  = Vec (Ty) n


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

eval : ∀ {n : ℕ} {ctx : Ctx n} {ty : Ty}  → Exp ctx ty → HVec evalTy ctx → (evalTy ty)
eval (Var x) ctx = hlookup  ctx x -- hlookup x ctx
eval (Lam exp) ctx = λ x → eval exp (x ∷ᴴ ctx)
eval CZero ctx = 0
eval Suc ctx = λ x → suc x
eval (App f x) ctx = (eval f ctx) (eval x ctx)
eval (Nat n) ctx = n
eval (PrecT h acc counter) ctx = para (eval h ctx) (eval acc ctx) (eval counter ctx)



-- -- ------------------------------------------------------------------------------
-- -- -- uncurryH
-- -- ------------------------------------------------------------------------------


countArgs : Ty → ℕ
countArgs TyNat = 0
countArgs (tyA ⇒ tyB) = suc (countArgs tyB)

getArgs : (ty : Ty) -> Vec Ty (countArgs ty) 
getArgs TyNat = []
getArgs (ty ⇒ tyB) = ty ∷ getArgs tyB



uncurryH : ∀ {ty : Ty} → evalTy ty → HVec evalTy ( (getArgs ty))  → ℕ
uncurryH {TyNat} exp hxs = exp
uncurryH {tyA ⇒ tyB} f (x ∷ᴴ hxs) = uncurryH (f x) hxs



eval' : ∀ {n : ℕ} {ctx : Ctx n} {ty : Ty}  → Exp ctx ty → HVec evalTy ctx → HVec evalTy (getArgs ty) → ℕ
eval' exp ctx = uncurryH (eval exp ctx)



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
             eval' (prepLambdas ys xs exp) ys' (xs' ++ᴴ   args)  ≡ eval' exp (xs' ++rᴴ ys') args
prepLambdasEval .[] ys exp []ᴴ ys' args = refl
prepLambdasEval (x ∷ xs) ys exp (x' ∷ᴴ xs') ys' args rewrite prepLambdasEval xs (x ∷ ys) exp xs' (x' ∷ᴴ ys') args = refl

prepLambdasEvalClose : ∀ {n : ℕ} {ty : Ty} (xs : Vec Ty n )  (exp : Exp (xs ++r []) ty) (xs' : HVec evalTy xs )  (args : HVec evalTy (getArgs ty)) → 
             eval' (prepLambdas [] xs exp) []ᴴ (xs' ++ᴴ   args)  ≡ eval' exp (xs' ++rᴴ []ᴴ) args
prepLambdasEvalClose xs exp xs' args = prepLambdasEval xs [] exp xs' []ᴴ args


------------------------------------------------------------------------------
-- constant zero-function
------------------------------

mkConstZero :  ∀ {n  : ℕ}  (xs : Vec Ty n ) → Exp [] (prepArgs xs TyNat) 
mkConstZero xs = prepLambdas [] xs CZero

{-# REWRITE  ++identityRᴴ #-}


evalMkConstZero : ∀ {n  : ℕ}  (xs : Vec Ty n ) (xs' : HVec evalTy xs) → eval' (mkConstZero xs)  []ᴴ  xs'  ≡ 0
evalMkConstZero xs xs'  rewrite ++identityRᴴ xs' = prepLambdasEvalClose xs CZero xs' []ᴴ

------------------------------------------------------------------------------
-- projection
------------------------------------------------------------------------------
{-# REWRITE inject+0 lkupfromN' lkupfromN lookupOP lookupOpRev #-}

hlookupFromN' : ∀ {S : Set} {F : S → Set} {m n o : ℕ}
  {xs : Vec S m} {ys : Vec S (suc n + o)}
  (xs' : HVec F xs) (ys' : HVec F ys) →
  hlookup (xs' ++rᴴ ys') (fromℕ (m + n) ↑ˡ o) ≡
    hlookup ys' (fromℕ n ↑ˡ o)
hlookupFromN' []ᴴ (y ∷ᴴ ys') = refl
hlookupFromN' {m = suc m} {n} {o} (x ∷ᴴ xs') (y ∷ᴴ ys') =
  hlookupFromN' {m = m} {n = suc n} {o} xs' (x ∷ᴴ (y ∷ᴴ ys'))

hlookupFromN : ∀ {S : Set} {F : S → Set} {m n : ℕ}
  {xs : Vec S m} {ys : Vec S n} {y : S}
  (xs' : HVec F xs) (y' : F y) (ys' : HVec F ys) →
  hlookup (xs' ++rᴴ (y' ∷ᴴ ys')) (fromℕ m ↑ˡ n) ≡ y'
hlookupFromN xs' y' ys' = hlookupFromN' xs' (y' ∷ᴴ ys')

hlookupOP : ∀ {S : Set} {F : S → Set} {m n : ℕ}
  {xs : Vec S n} {ys : Vec S m} (f : Fin n)
  (xs' : HVec F xs) (ys' : HVec F ys) →
  hlookup (xs' ++rᴴ ys') (opposite f ↑ˡ m) ≡ hlookup xs' f
hlookupOP zero (x ∷ᴴ xs') ys' = hlookupFromN xs' x ys'
hlookupOP (suc f) (x ∷ᴴ xs') ys' = hlookupOP f xs' (x ∷ᴴ ys')

hlookupOpRev : ∀ {S : Set} {F : S → Set} {n : ℕ}
  {xs : Vec S n} (f : Fin n) (xs' : HVec F xs) →
  hlookup (xs' ++rᴴ []ᴴ) (opposite f) ≡ hlookup xs' f
hlookupOpRev f xs' = hlookupOP f xs' []ᴴ

mkProj : ∀ {n  : ℕ}  (xs : Vec Ty n ) → (f : Fin n)  →  Exp [] (prepArgs (xs) (lookup (xs) ( f))) 
mkProj xs f = prepLambdas [] ( xs)  (Var (opposite f))

evalMkProj : ∀ {n : ℕ} {xs : Vec Ty n} (f : Fin n)
  (xs' : HVec evalTy xs) (args : HVec evalTy (getArgs (lookup xs f)))
  → eval' (mkProj xs f) []ᴴ (xs' ++ᴴ args) ≡ uncurryH (hlookup xs' f) args
evalMkProj {xs = xs} f xs' args =
  trans
    (prepLambdasEvalClose xs (Var (opposite f)) xs' args)
    (cong (λ x → uncurryH x args) (hlookupOpRev f xs'))
