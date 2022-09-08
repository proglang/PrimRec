{-# OPTIONS --rewriting --prop -v rewriting:50 #-}

module System-T where



open import Data.Fin using (Fin; suc; zero; fromℕ; opposite; raise; inject+; inject₁)
open import Data.Nat using (ℕ; suc; zero; _∸_; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; +-comm)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head; init; reverse; last; foldl) -- ; _ʳ++_) 
open import Function.Base using (const; _∘′_; id; _∘_)
-- open import Data.Vec.Base using (_ʳ++_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Equality.Rewrite


open import PR-Nat
open import Utils
open import HVec



-- size of context and number of arguments

data Exp : ℕ → ℕ  → Set where
    Var : Fin n → Exp   n zero
    Lam : Exp (suc n) m → Exp n (suc m)
    CZero :  Exp n zero
    Suc : Exp n (suc zero)
    App : Exp n (suc m) → Exp n (zero) → Exp n m
    Nat : ℕ  → Exp n zero

evalST : Exp n m → Vec ℕ n → Vec ℕ m → ℕ 
evalST (Var x) ctx args = lookup ctx x
evalST (Lam exp) ctx (x ∷ args) = evalST exp (x ∷ ctx) args
evalST CZero ctx args = 0
evalST Suc ctx [ x ] = suc x
evalST (App f x) ctx args = evalST f ctx ( evalST x ctx [] ∷ args)
evalST (Nat n) _ [] = n

evalSTClosed : Exp zero m → Vec ℕ m → ℕ
evalSTClosed exp args = evalST exp [] args


------------------------------------------------------------------------------
-- helper
------------------------------------------------------------------------------
{-# REWRITE +-identityʳ +-suc #-}

-- prepLambdas : (n : ℕ) → (m : ℕ) →  Exp (m + n) o -> Exp n (m + o)
-- prepLambdas n zero  exp = exp
-- prepLambdas n (suc m) exp = Lam (prepLambdas  (suc n) m exp)

prepLambdas' : (n : ℕ) → (m : ℕ) →  Exp (n + m) o -> Exp n (o + m)
prepLambdas' n zero  exp = exp
prepLambdas' n (suc m) exp    = Lam (prepLambdas'  (suc n) m exp)
------------------------------------------------------------------------------
-- constant zero-function
------------------------------------------------------------------------------

mkConstZero :  {n : ℕ} → (m : ℕ) → Exp n m 
mkConstZero {n} m = prepLambdas' n m CZero
-- mkConstZero zero = CZero
-- mkConstZero (suc m) = Lam (mkConstZero m)

------------------------------------------------------------------------------
-- projection
------------------------------------------------------------------------------


convProjHelper : (m : ℕ) → (n : ℕ) → Fin (n + m)  →  Exp n m
-- convProjHelper zero n f  = Var f
-- convProjHelper (suc m) n f  = Lam (convProjHelper m (suc n) f)
convProjHelper m n f  = prepLambdas' n m (Var f)




myInject : ∀ {m} n → Fin m → Fin (n + m)
myInject n zero = zero
myInject n (suc f) = suc (myInject n f)


convProj :  (m : ℕ) → (n : ℕ) → Fin m  → Exp n m
convProj  m n f = convProjHelper m n (myInject n (opposite {m} f))


_++r_ : ∀ {m n} → Vec A m → Vec A n → Vec A (n + m)
(x ∷ xs)      ++r ys = xs ++r (x ∷ ys)
[] ++r ys =  ys


id' : ∀ {m n : ℕ } → Vec A (m + n) → Vec A (n + m)
id' {A} {m} {n} vs rewrite +-comm m n = vs


++r-reverse' : ∀ {A : Set} {m n : ℕ}  (xs : Vec A m) (ys : Vec A n) →    (xs ++r ys) ≡ id' {A} {m} {n} ((reverse xs) ++ ys)
++r-reverse' {A} {zero} {n} [] ys = {!   !} 
++r-reverse' (x ∷ xs) ys = {!   !}

++r-reverse : ∀ {m} (xs : Vec A m) → xs ++r [] ≡ (reverse xs)
++r-reverse [] = refl
++r-reverse (x ∷ xs) = {!   !}


lookupOp' :  ∀ {A : Set} {n} (f : Fin n) (xs : Vec A n) → lookup (reverse xs) (opposite f)  ≡ lookup  (xs) f
lookupOp' zero [ x ] = refl
lookupOp' zero (x ∷ y ∷ xs) = {!   !} 
lookupOp' {A} {suc (suc n)} (suc f) (x ∷ y ∷ xs)  = {!    !} 


eqProj' : ∀  {m n : ℕ} (f : Fin (n + (suc m)) ) (ctx : Vec ℕ n) (args : Vec ℕ (suc m))  → evalST (convProjHelper (suc m) n f) ctx args ≡ lookup ((  args) ++r ctx) ( f)
eqProj' {.zero} {n} f ctx [ x ] = refl
eqProj' {(suc m)} {n} f ctx (x ∷ y ∷ args) = eqProj' f  (( x ∷ ctx)) (y ∷ args) -- eqProj' f  (y ∷ x ∷ ctx) {!  args !}



eqProj'' : ∀  {n : ℕ} (f : Fin ((suc n)) ) (args : Vec ℕ (suc n))  → evalST (convProjHelper (suc n) zero (opposite f)) [] args ≡ lookup args f
eqProj'' {n} f vs = evalST (convProjHelper (suc n) zero (opposite f)) [] vs ≡⟨ eqProj' (opposite f) [] vs ⟩ lookup (vs ++r []) (opposite f) ≡⟨⟩ {!   !} ≡⟨⟩ {!   !}


eqProj''' : ∀  {n : ℕ} (f : Fin ((suc n)) ) (vs : Vec ℕ (suc n))  → lookup (vs ++r []) (opposite f) ≡ lookup vs f
eqProj''' {n} zero (x ∷ vs) = {!   !}
eqProj''' {n} (suc f) (x ∷ vs) = {!   !}
-- ------------------------------------------------------------------------------
-- -- conversion
-- ------------------------------------------------------------------------------


prToST : (n : ℕ) → (m : ℕ) → PR m → Exp n m 
prToST n m Z = mkConstZero m
prToST n .1 σ = Suc
prToST n m (π i) = convProj m n ( i)
prToST n m (C pr x) = {!   !}
prToST n .(suc _) (P pr pr₁) = {!   !}


prToST' : (m : ℕ) → PR m → Exp zero m 
prToST' m  pr = prToST zero m pr

eqPrST0 : ∀ ( pr : PR zero) → eval pr [] ≡ evalSTClosed (prToST' zero  pr) []
eqPrST0 Z = refl
eqPrST0 (C pr x)  = {!   !}


eqPrST1 : ∀ ( pr : PR 1) (n : ℕ ) → eval pr [ n ] ≡ evalSTClosed (prToST' 1 pr) [ n ]
eqPrST1 Z n = refl
eqPrST1 σ n = refl
eqPrST1 (π zero) n = refl
eqPrST1 (C pr x) n = {!   !}
eqPrST1 (P pr pr₁) n = {!   !}


eqPrST2 : ∀ ( pr : PR 2) (v : Vec ℕ 2 ) → eval pr v ≡ evalSTClosed (prToST' 2 pr) v
eqPrST2 Z [ n , m ] = refl
eqPrST2 (π zero) [ n , m ]  = refl
eqPrST2 (π (suc zero)) [ n , m ] = refl
eqPrST2 (C pr x) v = {!   !}
eqPrST2 (P pr pr₁) v = {!   !}


eqPrST3 : ∀ ( pr : PR 3) (v : Vec ℕ 3 ) → eval pr v ≡ evalSTClosed (prToST' 3  pr) v
eqPrST3 Z (n ∷ [ m , o ]) = refl
eqPrST3 (π zero) (n ∷ [ m , o ]) = refl
eqPrST3 (π (suc zero)) (n ∷ [ m , o ]) = refl
eqPrST3 (π (suc (suc zero))) (n ∷ [ m , o ]) = refl
eqPrST3 (C pr x) (n ∷ [ m , o ]) = {!   !}
eqPrST3 (P pr pr₁) (n ∷ [ m , o ]) = {!   !}

eqPrST4 : ∀ ( pr : PR 4) (v : Vec ℕ 4 ) → eval pr v ≡ evalSTClosed (prToST' 4  pr) v
eqPrST4 Z v = {!   !}
eqPrST4 (π zero) (x ∷ x₁ ∷ [ x₂ , x₃ ]) = refl
eqPrST4 (π (suc zero)) (x ∷ x₁ ∷ [ x₂ , x₃ ]) = refl
eqPrST4 (π (suc (suc zero))) (x ∷ x₁ ∷ [ x₂ , x₃ ]) = refl
eqPrST4 (π (suc (suc (suc zero)))) (x ∷ x₁ ∷ [ x₂ , x₃ ]) = refl
eqPrST4 (C pr x) v = {!   !}
eqPrST4 (P pr pr₁) v = {!   !}

eqPrSTZ' : ∀  (n m : ℕ ) (xs : Vec ℕ n )  (ys : Vec ℕ m )→ 0 ≡ evalST (mkConstZero m) xs ys
eqPrSTZ' n zero xs ys = refl
eqPrSTZ' n (suc m) xs (y ∷ ys) = eqPrSTZ' (suc n) m (y ∷ xs) ys

eqPrSTZ : ∀  (n : ℕ ) (v : Vec ℕ n ) → 0 ≡ evalSTClosed (prToST' n Z) v
eqPrSTZ n v = eqPrSTZ' zero n [] v

eqPrSTn : ∀  (n : ℕ ) ( pr : PR n) (v : Vec ℕ n ) → eval pr v ≡ evalSTClosed (prToST' n  pr) v
eqPrSTn n Z v = eqPrSTZ n v
eqPrSTn 1 σ [ x ] = refl
eqPrSTn (suc n) (π i) (vs) = {!   !} --helper12 i ((v ∷ vs)) []
eqPrSTn n (C pr x) v = {!   !}
eqPrSTn .(suc _) (P pr pr₁) v = {!   !}                

-- ∀ {m} (i : Fin m) lookup vs i ≡ evalSTClosed (prToST' (suc n) (π i)) vs


-- ------------------------------------------------------------------------------
-- -- embedding
-- ------------------------------------------------------------------------------

-- data Ty : Set where
--     TyNat : Ty
--     _⇒_ : Ty → Ty → Ty


-- Ctx : ℕ → Set 
-- Ctx n  = Vec (Ty) n


-- DBI : ∀ {n : ℕ} -> Ctx n  -> Ty -> Set
-- DBI = HIndex


-- -- data DBI : ∀ {n : ℕ} -> Ctx n  -> Ty -> Set where
-- --     ZDB : ∀ {n : ℕ} {ts : Ctx n}  {t} → DBI (t ∷ ts) t
-- --     SDB : ∀ {n : ℕ} {ts : Ctx n} {t t' : Ty} → DBI (ts) t → DBI (t' ∷ ts) t

-- data Exp' : ∀ {n : ℕ} -> Ctx n  -> Ty -> Set where
--     Var' : ∀ {n : ℕ} {ctx : Ctx n} {ty} → DBI ctx ty → Exp' ctx ty
--     Lam'  : ∀ {n : ℕ} {ctx : Ctx n} { tyA tyB} → Exp' (tyA ∷ ctx) tyB → Exp' ctx  (tyA ⇒ tyB)
--     CZero' :   ∀ {n : ℕ} {ctx : Ctx n} → Exp' ctx TyNat
--     Suc' : ∀ {n : ℕ} {ctx : Ctx n} → Exp' ctx (TyNat ⇒ TyNat)
--     App' : ∀ {n : ℕ} {ctx : Ctx n} {tyA tyB} →   Exp' ctx (tyA ⇒ tyB) → Exp' ctx tyA → Exp' ctx tyB
--     Nat' : ∀ {n : ℕ} {ctx : Ctx n} → ℕ → Exp' ctx TyNat

-- ℕtoTy : ℕ → Ty
-- ℕtoTy zero = TyNat
-- ℕtoTy (suc n) = TyNat ⇒  (ℕtoTy n)
 
-- ℕtoCtx : (n : ℕ) → Ctx n
-- ℕtoCtx n = repeat n TyNat


-- finToDBI : ∀ {n : ℕ} → (Fin n) → DBI (ℕtoCtx n) TyNat
-- finToDBI zero = ZI
-- finToDBI (suc f) = SI (finToDBI f)

-- embedd : ∀ {n m} → Exp n m → Exp' {n} (ℕtoCtx n) (ℕtoTy m) 
-- embedd (Var x) = Var' (finToDBI x)
-- embedd (Lam exp) = Lam' (embedd exp)
-- embedd CZero = CZero'
-- embedd Suc = Suc'
-- embedd (App f x) = App' (embedd f) (embedd x)
-- embedd (Nat n) = Nat' n

-- evalTy : Ty → Set
-- evalTy TyNat = ℕ
-- evalTy (tyA ⇒ tyB) = (evalTy tyA) → (evalTy tyB)

-- evalExp' : ∀ {n : ℕ} {ctx : Ctx n} {ty : Ty}  → Exp' ctx ty → HVec evalTy ctx → (evalTy ty)
-- evalExp' (Var' x) ctx = lkupH x ctx
-- evalExp' (Lam' exp) ctx = λ x → evalExp' exp (x ∷ᴴ ctx)
-- evalExp' CZero' ctx = 0
-- evalExp' Suc' ctx = λ x → suc x
-- evalExp' (App' f x) ctx = (evalExp' f ctx) (evalExp' x ctx)
-- evalExp' (Nat' n) ctx = n

-- countArgs : Ty → ℕ
-- countArgs TyNat = 0
-- countArgs (tyA ⇒ tyB) = suc (countArgs tyB)

-- getArgs : (ty : Ty) -> Vec Ty (countArgs ty) 
-- getArgs TyNat = []
-- getArgs (ty ⇒ tyB) = ty ∷ getArgs tyB

-- init' : ∀  {n : ℕ} {A : Set} → Vec A n → Vec A (n ∸ 1 )
-- init' [] = []
-- init' [ x ] = []
-- init' (x ∷ y ∷ vs) = x ∷ init (y ∷ vs)

-- uncurryH : ∀ {ty : Ty} → evalTy ty → HVec evalTy ( (getArgs ty))  → ℕ
-- uncurryH {TyNat} exp hxs = exp
-- uncurryH {tyA ⇒ tyB} f (x ∷ᴴ hxs) = uncurryH (f x) hxs

-- toHVec' : ∀  {n} → (v : Vec ℕ n) → HVec (evalTy) (repeat n TyNat )
-- toHVec' [] = []ᴴ
-- toHVec' (x ∷ v) = x ∷ᴴ toHVec' v

-- toHVecCons  : ∀  {n v} → (vs : Vec ℕ n) → toHVec' (v ∷ vs) ≡ v ∷ᴴ toHVec' vs
-- toHVecCons vs = refl

-- evalExp'' : ∀ {n : ℕ} {ctx : Ctx n} {ty : Ty}  → Exp' ctx ty → HVec evalTy ctx → HVec evalTy (getArgs ty) → ℕ
-- evalExp'' exp ctx = uncurryH (evalExp' exp ctx)

-- helper' : ∀ (m : ℕ ) → repeat (countArgs (ℕtoTy m)) TyNat ≡ getArgs (ℕtoTy m) 
-- helper' zero = refl
-- helper' (suc n) = cong (λ xs → TyNat ∷ xs) (helper' n)

-- helper'' :  ∀ {m : ℕ } → HVec evalTy (repeat (countArgs (ℕtoTy m)) TyNat) → HVec evalTy (getArgs (ℕtoTy m))  
-- helper''  {m} hxs rewrite helper' m = hxs

-- helper''' : ∀ {m} → (countArgs (ℕtoTy m)) ≡ m 
-- helper''' {zero} = refl
-- helper''' {suc m} = cong suc (helper''' {m})

-- helper'''' : ∀ {A : Set} {m} → Vec A m → Vec A (countArgs (ℕtoTy m))
-- helper'''' {A}{m} vs rewrite ((helper''' {m})) = vs

-- helper4 : ∀ (n : ℕ) → countArgs (ℕtoTy n) ≡ n 
-- helper4 zero = refl
-- helper4 (suc n) = cong suc (helper4 n)


-- {-# REWRITE helper' helper''' helper4  #-}

-- helper3 : ∀ (n : ℕ) → repeat n TyNat ≡ getArgs (ℕtoTy n)
-- helper3 zero = refl
-- helper3 (suc n) = cong (λ vs → TyNat ∷ vs) (helper3 n)


-- {-# REWRITE helper3  #-}


-- helper1 : ∀ {n : ℕ} (ctx : Vec ℕ n) (x : Fin n)  → lookup ctx x ≡ evalExp'' (Var' (finToDBI x)) (toHVec' ctx) ([]ᴴ)
-- helper1  (x ∷ ctx) zero = refl
-- helper1 (x₁ ∷ ctx) (suc x) rewrite helper1  ctx x  = refl


-- --  
 
-- sound-embedd : ∀ {n m : ℕ} (exp : Exp n m)  (ctx : Vec ℕ n) (args : Vec ℕ m) → (evalST exp ctx args)  ≡  (evalExp'' (embedd  exp) (toHVec' ctx) ) ( (toHVec'   ( args)))
-- sound-embedd (Var x) ctx []   = helper1 ctx x
-- sound-embedd {n} {suc m} (Lam exp) (ctx) (x ∷ args) rewrite sound-embedd exp (x ∷ ctx) args = refl
-- sound-embedd CZero ctx args = refl
-- sound-embedd Suc ctx [ n ] = refl 
-- sound-embedd (App f x) ctx args rewrite sound-embedd x ctx []  | sound-embedd f ctx ( (evalExp' (embedd x) (toHVec' ctx)) ∷ args) = refl
-- sound-embedd (Nat n) ctx [] = refl
     