{-# OPTIONS --safe #-}

module System-T where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_; lookup)

----------------------------------------------------------------------
-- A safe presentation of Gödel's System T.
--
-- The previous version mixed the syntax/evaluator with helper proofs
-- for closed constants and projections that relied on Agda rewrite
-- pragmas.  Since --safe rejects --rewriting, this module now contains
-- the intrinsic syntax and evaluator directly, together with the small
-- eliminators used by the rest of the formalization.
----------------------------------------------------------------------

data Ty : Set where
  TyNat : Ty
  _⇒_   : Ty → Ty → Ty

Ctx : ℕ → Set
Ctx n = Vec Ty n

data Exp : ∀ {n : ℕ} → Ctx n → Ty → Set where
  Var : ∀ {n : ℕ} {ctx : Ctx n}
    → (f : Fin n)
    → Exp ctx (lookup ctx f)
  Lam : ∀ {n : ℕ} {ctx : Ctx n} {tyA tyB : Ty}
    → Exp (tyA ∷ ctx) tyB
    → Exp ctx (tyA ⇒ tyB)
  CZero : ∀ {n : ℕ} {ctx : Ctx n}
    → Exp ctx TyNat
  Suc : ∀ {n : ℕ} {ctx : Ctx n}
    → Exp ctx (TyNat ⇒ TyNat)
  App : ∀ {n : ℕ} {ctx : Ctx n} {tyA tyB : Ty}
    → Exp ctx (tyA ⇒ tyB)
    → Exp ctx tyA
    → Exp ctx tyB
  Nat : ∀ {n : ℕ} {ctx : Ctx n}
    → ℕ
    → Exp ctx TyNat
  PrecT : ∀ {n : ℕ} {ctx : Ctx n} {ty : Ty}
    → Exp ctx (ty ⇒ (TyNat ⇒ ty))
    → Exp ctx ty
    → Exp ctx TyNat
    → Exp ctx ty

data HVec {S : Set} (F : S → Set) : ∀ {n : ℕ} → Vec S n → Set where
  []ᴴ  : HVec F []
  _∷ᴴ_ : ∀ {n s ss} → F s → HVec F {n} ss → HVec F (s ∷ ss)

hlookup : ∀ {S : Set} {n : ℕ} {ss : Vec S n} {F : S → Set}
  → HVec F ss
  → (i : Fin n)
  → F (lookup ss i)
hlookup {ss = s ∷ ss} (a ∷ᴴ a*) Fin.zero = a
hlookup {ss = s ∷ ss} (a ∷ᴴ a*) (Fin.suc i) = hlookup a* i

para : ∀ {A : Set} → (A → ℕ → A) → A → ℕ → A
para h z zero = z
para h z (suc n) = h (para h z n) n

evalTy : Ty → Set
evalTy TyNat = ℕ
evalTy (tyA ⇒ tyB) = evalTy tyA → evalTy tyB

eval : ∀ {n : ℕ} {ctx : Ctx n} {ty : Ty}
  → Exp ctx ty
  → HVec evalTy ctx
  → evalTy ty
eval (Var x) ctx = hlookup ctx x
eval (Lam exp) ctx = λ x → eval exp (x ∷ᴴ ctx)
eval CZero ctx = zero
eval Suc ctx = suc
eval (App f x) ctx = eval f ctx (eval x ctx)
eval (Nat n) ctx = n
eval (PrecT h acc counter) ctx =
  para (eval h ctx) (eval acc ctx) (eval counter ctx)

countArgs : Ty → ℕ
countArgs TyNat = zero
countArgs (tyA ⇒ tyB) = suc (countArgs tyB)

getArgs : (ty : Ty) → Vec Ty (countArgs ty)
getArgs TyNat = []
getArgs (tyA ⇒ tyB) = tyA ∷ getArgs tyB

uncurryH : ∀ {ty : Ty} → evalTy ty → HVec evalTy (getArgs ty) → ℕ
uncurryH {TyNat} exp []ᴴ = exp
uncurryH {tyA ⇒ tyB} f (x ∷ᴴ hxs) = uncurryH (f x) hxs

eval' : ∀ {n : ℕ} {ctx : Ctx n} {ty : Ty}
  → Exp ctx ty
  → HVec evalTy ctx
  → HVec evalTy (getArgs ty)
  → ℕ
eval' exp ctx = uncurryH (eval exp ctx)
