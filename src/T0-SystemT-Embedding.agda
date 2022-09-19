{-# OPTIONS --rewriting --prop -v rewriting:50 #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _∸_)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; init; last) -- ; _ʳ++_) 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂; _≗_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Equality.Rewrite
open import System-T using (Exp; para; evalST; evalSTClosed; ext2)

open System-T.Exp
open import PR-Nat
open import Utils
open import HVec

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

data Exp' : ∀ {n : ℕ} -> Ctx n  -> Ty -> Set where
    Var' : ∀ {n : ℕ} {ctx : Ctx n} {ty} → DBI ctx ty → Exp' ctx ty
    Lam'  : ∀ {n : ℕ} {ctx : Ctx n} { tyA tyB} → Exp' (tyA ∷ ctx) tyB → Exp' ctx  (tyA ⇒ tyB)
    CZero' :   ∀ {n : ℕ} {ctx : Ctx n} → Exp' ctx TyNat
    Suc' : ∀ {n : ℕ} {ctx : Ctx n} → Exp' ctx (TyNat ⇒ TyNat)
    App' : ∀ {n : ℕ} {ctx : Ctx n} {tyA tyB} →   Exp' ctx (tyA ⇒ tyB) → Exp' ctx tyA → Exp' ctx tyB
    Nat' : ∀ {n : ℕ} {ctx : Ctx n} → ℕ → Exp' ctx TyNat
    PRecT' : ∀ {n : ℕ} {ctx : Ctx n}{ty} → Exp' ctx (ty ⇒ (TyNat ⇒ ty)) → Exp' ctx (ty) → Exp' ctx (TyNat) → Exp' ctx (ty)


ℕtoTy : ℕ → Ty
ℕtoTy zero = TyNat
ℕtoTy (suc n) = TyNat ⇒  (ℕtoTy n)
 
ℕtoCtx : (n : ℕ) → Ctx n
ℕtoCtx n = repeat n TyNat


finToDBI : ∀ {n : ℕ} → (Fin n) → DBI (ℕtoCtx n) TyNat
finToDBI zero = ZI
finToDBI (suc f) = SI (finToDBI f)

embedd : ∀ {n m} → Exp n m → Exp' {n} (ℕtoCtx n) (ℕtoTy m) 
embedd (Var x) = Var' (finToDBI x)
embedd (Lam exp) = Lam' (embedd exp)
embedd CZero = CZero'
embedd Suc = Suc'
embedd (App f x) = App' (embedd f) (embedd x)
embedd (Nat n) = Nat' n
embedd (PRecT h acc counter) = PRecT' (embedd h) (embedd acc) (embedd counter)

evalTy : Ty → Set
evalTy TyNat = ℕ
evalTy (tyA ⇒ tyB) = (evalTy tyA) → (evalTy tyB)

evalExp' : ∀ {n : ℕ} {ctx : Ctx n} {ty : Ty}  → Exp' ctx ty → HVec evalTy ctx → (evalTy ty)
evalExp' (Var' x) ctx = lkupH x ctx
evalExp' (Lam' exp) ctx = λ x → evalExp' exp (x ∷ᴴ ctx)
evalExp' CZero' ctx = 0
evalExp' Suc' ctx = λ x → suc x
evalExp' (App' f x) ctx = (evalExp' f ctx) (evalExp' x ctx)
evalExp' (Nat' n) ctx = n
evalExp' (PRecT' h acc counter) ctx = para (evalExp' h ctx) (evalExp' acc ctx) (evalExp' counter ctx)

countArgs : Ty → ℕ
countArgs TyNat = 0
countArgs (tyA ⇒ tyB) = suc (countArgs tyB)

getArgs : (ty : Ty) -> Vec Ty (countArgs ty) 
getArgs TyNat = []
getArgs (ty ⇒ tyB) = ty ∷ getArgs tyB

init' : ∀  {n : ℕ} {A : Set} → Vec A n → Vec A (n ∸ 1 )
init' [] = []
init' [ x ] = []
init' (x ∷ y ∷ vs) = x ∷ init (y ∷ vs)

uncurryH : ∀ {ty : Ty} → evalTy ty → HVec evalTy ( (getArgs ty))  → ℕ
uncurryH {TyNat} exp hxs = exp
uncurryH {tyA ⇒ tyB} f (x ∷ᴴ hxs) = uncurryH (f x) hxs

toHVec' : ∀  {n} → (v : Vec ℕ n) → HVec (evalTy) (repeat n TyNat )
toHVec' [] = []ᴴ
toHVec' (x ∷ v) = x ∷ᴴ toHVec' v



evalExp'' : ∀ {n : ℕ} {ctx : Ctx n} {ty : Ty}  → Exp' ctx ty → HVec evalTy ctx → HVec evalTy (getArgs ty) → ℕ
evalExp'' exp ctx = uncurryH (evalExp' exp ctx)

helper' : ∀ (m : ℕ ) → repeat (countArgs (ℕtoTy m)) TyNat ≡ getArgs (ℕtoTy m) 
helper' zero = refl
helper' (suc n) = cong (λ xs → TyNat ∷ xs) (helper' n)

helper''' : ∀ {m} → (countArgs (ℕtoTy m)) ≡ m 
helper''' {zero} = refl
helper''' {suc m} = cong suc (helper''' {m})


{-# REWRITE helper' helper''' #-}

helper3 : ∀ (n : ℕ) → repeat n TyNat ≡ getArgs (ℕtoTy n)
helper3 zero = refl
helper3 (suc n) = cong (λ vs → TyNat ∷ vs) (helper3 n)


{-# REWRITE helper3  #-}


convVarSound : ∀ {n : ℕ} (ctx : Vec ℕ n) (x : Fin n)  → lookup ctx x ≡ evalExp'' (Var' (finToDBI x)) (toHVec' ctx) ([]ᴴ)
convVarSound  (x ∷ ctx) zero = refl
convVarSound (x₁ ∷ ctx) (suc x) rewrite convVarSound  ctx x  = refl

 
sound-embedd : ∀ {n m : ℕ} (exp : Exp n m)  (ctx : Vec ℕ n) (args : Vec ℕ m) → (evalST exp ctx args)  ≡  (evalExp'' (embedd  exp) (toHVec' ctx) ) ( (toHVec'   ( args)))
sound-embedd (Var x) ctx []   = convVarSound ctx x
sound-embedd {n} {suc m} (Lam exp) (ctx) (x ∷ args) rewrite sound-embedd exp (x ∷ ctx) args = refl
sound-embedd CZero ctx args = refl
sound-embedd Suc ctx [ n ] = refl 
sound-embedd (App f x) ctx args rewrite sound-embedd x ctx []  | sound-embedd f ctx ( (evalExp' (embedd x) (toHVec' ctx)) ∷ args) = refl
sound-embedd (Nat n) ctx [] = refl
sound-embedd (PRecT h acc n) ctx [] rewrite sound-embedd acc ctx [] | sound-embedd n ctx [] | ext2 (λ x y → sound-embedd h ctx [ x , y ]) = refl