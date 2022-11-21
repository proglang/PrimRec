{-# OPTIONS --rewriting --prop -v rewriting:50 #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _∸_)
open import Data.Vec using (Vec; []; _∷_; lookup)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Equality.Rewrite
import System-T0 as T0 --using (Exp; eval; evalClosed; ext2)

-- open System-T0.Exp
open import PR-Nat
open import Utils
open import HVec
open import EvalPConstructor using (para)
open import System-T
-- -- ------------------------------------------------------------------------------
-- -- -- embedding
-- -- ------------------------------------------------------------------------------


-- finToDBI : ∀ {n : ℕ} → (Fin n) → DBI (ℕtoCtx n) TyNat
-- finToDBI zero = ZI
-- finToDBI (suc f) = SI (finToDBI f)

ℕtoTy : ℕ → Ty
ℕtoTy zero = TyNat
ℕtoTy (suc n) = TyNat ⇒  (ℕtoTy n)
 
ℕtoCtx : (n : ℕ) → Ctx n
ℕtoCtx n = repeat n TyNat

lookupRepeat=id : ∀ {A : Set}{n : ℕ}(f : Fin n) (x : A) → lookup (repeat n x) f ≡ x
lookupRepeat=id  zero x = refl
lookupRepeat=id (suc f) x = lookupRepeat=id f x

{-# REWRITE  lookupRepeat=id #-}


embedd : ∀ {n m} → T0.Exp n m → Exp {n} (ℕtoCtx n) (ℕtoTy m) 
embedd (T0.Var x)  =   Var x   -- Var x -- (finToDBI x)
embedd (T0.Lam exp) = Lam (embedd exp)
embedd T0.CZero = CZero
embedd T0.Suc = Suc
embedd (T0.App f x) = App (embedd f) (embedd x)
embedd (T0.Nat n) = Nat n
embedd (T0.PRecT h acc counter) = PrecT (embedd h) (embedd acc) (embedd counter)




countArgs-ℕtoTy=id : ∀ {m} → (countArgs (ℕtoTy m)) ≡ m 
countArgs-ℕtoTy=id {zero} = refl
countArgs-ℕtoTy=id {suc m} = cong suc (countArgs-ℕtoTy=id {m})

{-# REWRITE  countArgs-ℕtoTy=id #-}

repeatCountArgs=getArgs : ∀ (m : ℕ ) → repeat (m) TyNat ≡ getArgs (ℕtoTy m) 
repeatCountArgs=getArgs zero = refl
repeatCountArgs=getArgs (suc n) = cong (λ xs → TyNat ∷ xs) (repeatCountArgs=getArgs n)


{-# REWRITE repeatCountArgs=getArgs  #-}

-- convVarSound : ∀ {n : ℕ} (ctx : Vec ℕ n) (x : Fin n)  → lookup ctx x ≡ evalExp' (Var (finToDBI x)) (toHVec' ctx) ([]ᴴ)
-- convVarSound  (x ∷ ctx) zero = refl
-- convVarSound (x₁ ∷ ctx) (suc x) rewrite convVarSound  ctx x  = refl

helper : ∀ {n : ℕ}(f : Fin n) →  (lookup (getArgs (ℕtoTy n)) f) ≡ TyNat
helper  zero = refl
helper (suc f) = helper f

{-# REWRITE helper  #-}

toHVec' : ∀  {n} → (v : Vec ℕ n) → HVec (evalTy) (repeat n TyNat )
toHVec' [] = []ᴴ
toHVec' (x ∷ v) = x ∷ᴴ toHVec' v


convVarSound : ∀  {n : ℕ} (ctx : Vec ℕ n) (x : Fin n)  → lookup ctx x ≡ hlookup (toHVec' ctx) x
convVarSound (x₁ ∷ ctx) zero = refl
convVarSound (x₁ ∷ ctx) (suc x) = convVarSound ctx x

sound-embedd : ∀ {n m : ℕ} (exp : T0.Exp n m)  (ctx : Vec ℕ n) (args : Vec ℕ m) → (T0.eval exp ctx args)  ≡  (evalExp' (embedd  exp) (toHVec' ctx) ) ( (toHVec'   ( args)))
sound-embedd {suc n} (T0.Var x) ctx []   = convVarSound ctx x 
sound-embedd {n} {suc m} (T0.Lam exp) (ctx) (x ∷ args) rewrite sound-embedd exp (x ∷ ctx) args = refl
sound-embedd T0.CZero ctx args = refl
sound-embedd T0.Suc ctx [ n ] = refl 
sound-embedd (T0.App f x) ctx args rewrite sound-embedd x ctx []  | sound-embedd f ctx ( (evalExp (embedd x) (toHVec' ctx)) ∷ args) = refl
sound-embedd (T0.Nat n) ctx [] = refl
sound-embedd (T0.PRecT h acc n) ctx [] rewrite sound-embedd acc ctx [] | sound-embedd n ctx [] | T0.ext2 (λ x y → sound-embedd h ctx [ x , y ]) = refl
  