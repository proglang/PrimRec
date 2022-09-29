{-# OPTIONS --rewriting --prop -v rewriting:50 #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _∸_)
open import Data.Vec using (Vec; []; _∷_; lookup)
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
-- -- ------------------------------------------------------------------------------
-- -- -- embedding
-- -- ------------------------------------------------------------------------------

data Ty : Set where
    TyNat : Ty
    _⇒_ : Ty → Ty → Ty


Ctx : ℕ → Set 
Ctx n  = Vec (Ty) n


DBI : ∀ {n : ℕ} -> Ctx n  -> Ty -> Set
DBI = HIndex


-- data DBI : ∀ {n : ℕ} -> Ctx n  -> Ty -> Set where
--     ZDB : ∀ {n : ℕ} {ts : Ctx n}  {t} → DBI (t ∷ ts) t
--     SDB : ∀ {n : ℕ} {ts : Ctx n} {t t' : Ty} → DBI (ts) t → DBI (t' ∷ ts) t

data Exp : ∀ {n : ℕ} -> Ctx n  -> Ty -> Set where
    Var : ∀ {n : ℕ} {ctx : Ctx n} {ty} → DBI ctx ty → Exp ctx ty
    Lam  : ∀ {n : ℕ} {ctx : Ctx n} { tyA tyB} → Exp (tyA ∷ ctx) tyB → Exp ctx  (tyA ⇒ tyB)
    CZero :   ∀ {n : ℕ} {ctx : Ctx n} → Exp ctx TyNat
    Suc : ∀ {n : ℕ} {ctx : Ctx n} → Exp ctx (TyNat ⇒ TyNat)
    App : ∀ {n : ℕ} {ctx : Ctx n} {tyA tyB} →   Exp ctx (tyA ⇒ tyB) → Exp ctx tyA → Exp ctx tyB
    Nat : ∀ {n : ℕ} {ctx : Ctx n} → ℕ → Exp ctx TyNat
    PrecT : ∀ {n : ℕ} {ctx : Ctx n}{ty} → Exp ctx (ty ⇒ (TyNat ⇒ ty)) → Exp ctx (ty) → Exp ctx (TyNat) → Exp ctx (ty)


ℕtoTy : ℕ → Ty
ℕtoTy zero = TyNat
ℕtoTy (suc n) = TyNat ⇒  (ℕtoTy n)
 
ℕtoCtx : (n : ℕ) → Ctx n
ℕtoCtx n = repeat n TyNat


finToDBI : ∀ {n : ℕ} → (Fin n) → DBI (ℕtoCtx n) TyNat
finToDBI zero = ZI
finToDBI (suc f) = SI (finToDBI f)

embedd : ∀ {n m} → T0.Exp n m → Exp {n} (ℕtoCtx n) (ℕtoTy m) 
embedd (T0.Var x) = Var (finToDBI x)
embedd (T0.Lam exp) = Lam (embedd exp)
embedd T0.CZero = CZero
embedd T0.Suc = Suc
embedd (T0.App f x) = App (embedd f) (embedd x)
embedd (T0.Nat n) = Nat n
embedd (T0.PRecT h acc counter) = PrecT (embedd h) (embedd acc) (embedd counter)

evalTy : Ty → Set
evalTy TyNat = ℕ
evalTy (tyA ⇒ tyB) = (evalTy tyA) → (evalTy tyB)

evalExp : ∀ {n : ℕ} {ctx : Ctx n} {ty : Ty}  → Exp ctx ty → HVec evalTy ctx → (evalTy ty)
evalExp (Var x) ctx = lkupH x ctx
evalExp (Lam exp) ctx = λ x → evalExp exp (x ∷ᴴ ctx)
evalExp CZero ctx = 0
evalExp Suc ctx = λ x → suc x
evalExp (App f x) ctx = (evalExp f ctx) (evalExp x ctx)
evalExp (Nat n) ctx = n
evalExp (PrecT h acc counter) ctx = para (evalExp h ctx) (evalExp acc ctx) (evalExp counter ctx)

countArgs : Ty → ℕ
countArgs TyNat = 0
countArgs (tyA ⇒ tyB) = suc (countArgs tyB)

getArgs : (ty : Ty) -> Vec Ty (countArgs ty) 
getArgs TyNat = []
getArgs (ty ⇒ tyB) = ty ∷ getArgs tyB

init' : ∀  {n : ℕ} {A : Set} → Vec A n → Vec A (n ∸ 1 )
init' [] = []
init' [ x ] = []
init' (x ∷ y ∷ vs) = x ∷ init' (y ∷ vs)

uncurryH : ∀ {ty : Ty} → evalTy ty → HVec evalTy ( (getArgs ty))  → ℕ
uncurryH {TyNat} exp hxs = exp
uncurryH {tyA ⇒ tyB} f (x ∷ᴴ hxs) = uncurryH (f x) hxs

toHVec' : ∀  {n} → (v : Vec ℕ n) → HVec (evalTy) (repeat n TyNat )
toHVec' [] = []ᴴ
toHVec' (x ∷ v) = x ∷ᴴ toHVec' v


evalExp' : ∀ {n : ℕ} {ctx : Ctx n} {ty : Ty}  → Exp ctx ty → HVec evalTy ctx → HVec evalTy (getArgs ty) → ℕ
evalExp' exp ctx = uncurryH (evalExp exp ctx)


countArgs-ℕtoTy=id : ∀ {m} → (countArgs (ℕtoTy m)) ≡ m 
countArgs-ℕtoTy=id {zero} = refl
countArgs-ℕtoTy=id {suc m} = cong suc (countArgs-ℕtoTy=id {m})

{-# REWRITE  countArgs-ℕtoTy=id #-}

repeatCountArgs=getArgs : ∀ (m : ℕ ) → repeat (m) TyNat ≡ getArgs (ℕtoTy m) 
repeatCountArgs=getArgs zero = refl
repeatCountArgs=getArgs (suc n) = cong (λ xs → TyNat ∷ xs) (repeatCountArgs=getArgs n)


{-# REWRITE repeatCountArgs=getArgs  #-}

convVarSound : ∀ {n : ℕ} (ctx : Vec ℕ n) (x : Fin n)  → lookup ctx x ≡ evalExp' (Var (finToDBI x)) (toHVec' ctx) ([]ᴴ)
convVarSound  (x ∷ ctx) zero = refl
convVarSound (x₁ ∷ ctx) (suc x) rewrite convVarSound  ctx x  = refl

 
sound-embedd : ∀ {n m : ℕ} (exp : T0.Exp n m)  (ctx : Vec ℕ n) (args : Vec ℕ m) → (T0.evalST exp ctx args)  ≡  (evalExp' (embedd  exp) (toHVec' ctx) ) ( (toHVec'   ( args)))
sound-embedd (T0.Var x) ctx []   = convVarSound ctx x
sound-embedd {n} {suc m} (T0.Lam exp) (ctx) (x ∷ args) rewrite sound-embedd exp (x ∷ ctx) args = refl
sound-embedd T0.CZero ctx args = refl
sound-embedd T0.Suc ctx [ n ] = refl 
sound-embedd (T0.App f x) ctx args rewrite sound-embedd x ctx []  | sound-embedd f ctx ( (evalExp (embedd x) (toHVec' ctx)) ∷ args) = refl
sound-embedd (T0.Nat n) ctx [] = refl
sound-embedd (T0.PRecT h acc n) ctx [] rewrite sound-embedd acc ctx [] | sound-embedd n ctx [] | T0.ext2 (λ x y → sound-embedd h ctx [ x , y ]) = refl
 