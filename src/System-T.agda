{-# OPTIONS --rewriting --prop -v rewriting:50 #-}

module System-T where



open import Data.Fin using (Fin; suc; zero; fromℕ; opposite; raise; inject+; inject₁; toℕ)
open import Data.Nat using (ℕ; suc; zero; _∸_; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; +-comm; +-assoc)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head; init; reverse; last; foldl) -- ; _ʳ++_) 
open import Data.Vec.Properties using (lookup-++ˡ; map-cong)
open import Function.Base using (const; _∘′_; id; _∘_; flip)
open import Data.Fin.Properties using (toℕ-fromℕ; fromℕ-toℕ) -- (++-assoc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂; _≗_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Equality.Rewrite
open import NatProperties using (assoc-comm-suc)
open import FinProperties using (inject+0; inject+1; inject+Add; inject+Eq)
open import VecProperties

open import PR-Nat
open import Utils
open import HVec



data Exp : ℕ → ℕ  → Set where
    Var : Fin n → Exp   n zero
    Lam : Exp (suc n) m → Exp n (suc m)
    CZero :  Exp n zero
    Suc : Exp n (suc zero)
    App : Exp n (suc m) → Exp n (zero) → Exp n m
    Nat : ℕ  → Exp n zero

evalST : ∀ {n m : ℕ} → Exp n m → Vec ℕ n → Vec ℕ m → ℕ 
evalST (Var x) ctx args = lookup ctx x
evalST (Lam exp) ctx (x ∷ args) = evalST exp (x ∷ ctx) args
evalST CZero ctx args = 0
evalST Suc ctx [ x ] = suc x
evalST (App f x) ctx args = evalST f ctx ( evalST x ctx [] ∷ args)
evalST (Nat n) _ [] = n

evalSTClosed : Exp zero m → Vec ℕ m → ℕ
evalSTClosed exp args = evalST exp [] args

raiseExP : ∀ {m n} (o) → Exp m n → Exp (m + o) n
raiseExP  {m} {n} o (Var x) =  Var (inject+ o  x   ) --rewrite +-comm m o 
raiseExP o (Lam exp) = Lam (raiseExP o exp)
raiseExP o CZero = CZero
raiseExP o Suc = Suc
raiseExP o (App f x) = App (raiseExP o f) (raiseExP o x)
raiseExP o (Nat x) = Nat x

raiseExPSound : ∀ {m n o} (exp : Exp m n) (ctx : Vec ℕ m)(ctx2 : Vec ℕ o)(args : Vec ℕ n) → evalST exp ctx args ≡ evalST (raiseExP o exp) (ctx ++ ctx2) args
raiseExPSound (Var x) (ctx) ctx2 args = sym (lookup-++ˡ ctx ctx2 x) -- lookup-++ˡ {! ctx  !} {!   !} x
raiseExPSound (Lam exp) ctx ctx2 (a ∷ args) rewrite raiseExPSound exp (a ∷ ctx) ctx2 args = refl
raiseExPSound CZero ctx ctx2 args = refl
raiseExPSound Suc ctx ctx2 [ x ] = refl
raiseExPSound {m}{n} {o} (App f x) ctx ctx2 args  rewrite raiseExPSound x ctx ctx2 []  | raiseExPSound f ctx ctx2  (evalST (raiseExP o x) (ctx ++ ctx2) [] ∷ args) = refl
raiseExPSound (Nat x) ctx ctx2 [] = refl


------------------------------------------------------------------------------
-- helper
------------------------------------------------------------------------------



prepLambdas' : ∀ {o} (n : ℕ) → (m : ℕ) →  Exp (m + n) o -> Exp n (o + m)
prepLambdas' {o} n zero exp   = exp
prepLambdas' {o} n (suc m) exp   = Lam (prepLambdas'  (suc n) m exp)


prepLambdasEval : ∀ {ctxLen argsLen : ℕ} (ctx : Vec ℕ ctxLen ) (args : Vec ℕ argsLen ) (exp) → evalST (prepLambdas' ctxLen argsLen exp) ctx args ≡ evalST exp (args ++r ctx) []
prepLambdasEval ctx [] exp = refl
prepLambdasEval ctx (x ∷ args) exp = prepLambdasEval ((x ∷ ctx)) args  exp

prepLambdasEvalClose : ∀ {argsLen : ℕ}  (args : Vec ℕ argsLen ) (exp : Exp argsLen zero) → evalSTClosed (prepLambdas' 0 argsLen exp) args ≡ evalST exp (fastReverse args) []
prepLambdasEvalClose = prepLambdasEval []


------------------------------------------------------------------------------
-- constant zero-function
------------------------------------------------------------------------------

mkConstZero :   (m : ℕ) → Exp zero m 
mkConstZero m = prepLambdas' zero m CZero


convZeroSound : ∀  (n : ℕ ) (v : Vec ℕ n ) → evalSTClosed (mkConstZero n) v  ≡ 0
convZeroSound n v = prepLambdasEvalClose v CZero 

------------------------------------------------------------------------------
-- projection
------------------------------------------------------------------------------


convProjHelper : ∀ {m} → Fin (m)  →  Exp zero m
convProjHelper {m} f  = prepLambdas' zero m (Var f)

{-# REWRITE inject+0  #-}


convProj : ∀ {m : ℕ } → Fin m  → Exp zero m
convProj  {m}  f = convProjHelper {m} (opposite {m} f)


convProjSoundHelper : ∀  {m : ℕ} (f : Fin (suc m ) ) (args : Vec ℕ (suc m))  → evalSTClosed (convProjHelper f)  args ≡ lookup (( fastReverse args) ) ( f)
convProjSoundHelper f args = prepLambdasEvalClose args (Var f)


convProjSound : ∀  {n : ℕ} (f : Fin ((suc n)) ) (args : Vec ℕ (suc n))  → evalSTClosed (convProjHelper  (opposite f)) args ≡ lookup args f
convProjSound {n} f vs = evalST (convProjHelper  (opposite f)) [] vs 
    ≡⟨ convProjSoundHelper (opposite f) vs ⟩ 
                        lookup (fastReverse vs) (opposite f) 
    ≡⟨ lookupOpRev f vs ⟩ 
                        (lookup vs f) ∎ 



-- ------------------------------------------------------------------------------
-- -- conversion
-- ------------------------------------------------------------------------------


convComp : ∀  {n m : ℕ }→ PR n → Vec (PR m) n → Exp zero m


prToST' : ∀ {m : ℕ} → PR m → Exp zero m 
prToST'  {m} Z = mkConstZero m
prToST'  σ = Suc
prToST' (π i) = convProj ( i)
prToST' (C f gs) = convComp f gs 
prToST'  (P pr pr₁) = {!   !}

prToST : (n : ℕ)  → PR m → Exp n m 
prToST n pr = raiseExP n (prToST' pr)

-- prToST' : (m : ℕ) → PR m → Exp zero m 
-- prToST' m  pr = prToST zero m pr

-- eqPrST0 : ∀ ( pr : PR zero) → eval pr [] ≡ evalSTClosed (prToST' zero  pr) []
-- eqPrST0 Z = refl
-- eqPrST0 (C pr x)  = {!   !}


-- eqPrST1 : ∀ ( pr : PR 1) (n : ℕ ) → eval pr [ n ] ≡ evalSTClosed (prToST' 1 pr) [ n ]
-- eqPrST1 Z n = refl
-- eqPrST1 σ n = refl
-- eqPrST1 (π zero) n = refl
-- eqPrST1 (C pr x) n = {!   !}
-- eqPrST1 (P pr pr₁) n = {!   !}


-- eqPrST2 : ∀ ( pr : PR 2) (v : Vec ℕ 2 ) → eval pr v ≡ evalSTClosed (prToST' 2 pr) v
-- eqPrST2 Z [ n , m ] = refl
-- eqPrST2 (π zero) [ n , m ]  = refl
-- eqPrST2 (π (suc zero)) [ n , m ] = refl
-- eqPrST2 (C pr x) v = {!   !}
-- eqPrST2 (P pr pr₁) v = {!   !}


-- eqPrST3 : ∀ ( pr : PR 3) (v : Vec ℕ 3 ) → eval pr v ≡ evalSTClosed (prToST' 3  pr) v
-- eqPrST3 Z (n ∷ [ m , o ]) = refl
-- eqPrST3 (π zero) (n ∷ [ m , o ]) = refl
-- eqPrST3 (π (suc zero)) (n ∷ [ m , o ]) = refl
-- eqPrST3 (π (suc (suc zero))) (n ∷ [ m , o ]) = refl
-- eqPrST3 (C pr x) (n ∷ [ m , o ]) = {!   !}
-- eqPrST3 (P pr pr₁) (n ∷ [ m , o ]) = {!   !}

-- eqPrST4 : ∀ ( pr : PR 4) (v : Vec ℕ 4 ) → eval pr v ≡ evalSTClosed (prToST' 4  pr) v
-- eqPrST4 Z v = {!   !}
-- eqPrST4 (π zero) (x ∷ x₁ ∷ [ x₂ , x₃ ]) = refl
-- eqPrST4 (π (suc zero)) (x ∷ x₁ ∷ [ x₂ , x₃ ]) = refl
-- eqPrST4 (π (suc (suc zero))) (x ∷ x₁ ∷ [ x₂ , x₃ ]) = refl
-- eqPrST4 (π (suc (suc (suc zero)))) (x ∷ x₁ ∷ [ x₂ , x₃ ]) = refl
-- eqPrST4 (C pr x) v = {!   !}
-- eqPrST4 (P pr pr₁) v = {!   !}

eqPrSTn : ∀  (n : ℕ ) ( pr : PR n) (v : Vec ℕ n ) → eval pr v ≡ evalSTClosed (prToST'   pr) v
eqPrSTn n Z v = sym (convZeroSound n v)
eqPrSTn 1 σ [ x ] = refl
eqPrSTn (suc n) (π i) (vs) =  sym (convProjSound i vs) -- sym (convProjSound i vs) --helper12 i ((v ∷ vs)) []
eqPrSTn n (C pr x) v = {!   !}
eqPrSTn .(suc _) (P pr pr₁) v = {!   !}                


-- -- ------------------------------------------------------------------------------
-- -- -- composition
-- -- ------------------------------------------------------------------------------

mkFinvec : ∀ (n : ℕ ) (m : ℕ ) → Vec (Fin (n + m)) n
mkFinvec zero m = []
mkFinvec (suc n) m = inject+ m  (fromℕ n ) ∷ (mkFinvec n (suc m))


arity : ∀ {n : ℕ} (pr : PR n) → ℕ
arity {n} _ = n

apply* : ∀ {n m o : ℕ} → Exp m (n + o) → Vec (Exp m zero) o  → Exp m n
apply* exp [] = exp
apply* exp (x ∷ vec) = apply* (App exp x) vec


evalApply*Eq :  ∀ {n m : ℕ} (exp : Exp n m) (args : Vec (Exp n zero) m) (ctx : Vec ℕ n) → evalST (apply* exp args) ctx  [] ≡ evalST exp  ctx (map (λ arg → evalST arg ctx []) args)
evalApply*Eq exp [] ctx = refl
evalApply*Eq {n} {suc m } exp (arg ∷ args) ctx rewrite evalApply*Eq {n} {m} (App exp arg) args ctx = refl

maplookupEq :  {n m : ℕ}  (vs : Vec ℕ n) (ys : Vec ℕ m) → (map (λ x → lookup (vs ++r ys) x) (mkFinvec n m)) ≡ vs
maplookupEq {.zero} [] ys = refl
maplookupEq {(suc n)} {m} (x ∷ vs) ys rewrite lookupOP' zero  (x ∷ vs) ys = cong (λ vec → x ∷ vec) (maplookupEq {n} {suc m} vs (x ∷ ys)) 


mapEvalVarsEq : ∀ {n : ℕ} (vs : Vec ℕ n) (exp : Exp n n) →  (map (λ arg → evalST arg (fastReverse vs) []) (map Var (mkFinvec n zero))) ≡ vs 
mapEvalVarsEq {n} vs exp    = 
        (map (λ arg → evalST arg (fastReverse vs) []) (map Var (mkFinvec n zero))) 
                ≡⟨ ∘-map (λ arg → evalST arg (fastReverse vs) []) Var (mkFinvec n zero) ⟩ 
        (map ((λ arg → evalST arg (fastReverse vs) []) ∘ Var) (mkFinvec n zero)) 
                ≡⟨⟩ 
        ((map (λ f → lookup (fastReverse vs) f ) (mkFinvec n zero)) 
                ≡⟨ maplookupEq vs [] ⟩ 
        vs ∎) 

evalApplyToVarsHelper1 : ∀ {n : ℕ} (vs : Vec ℕ n) (exp : Exp n n) → evalST exp (fastReverse vs) (map (λ arg → evalST arg (fastReverse vs) []) (map Var (mkFinvec n zero))) ≡ evalST exp (fastReverse vs) vs
evalApplyToVarsHelper1 vs exp rewrite mapEvalVarsEq vs exp = refl


applyToVars : ∀ {m o} → Exp (m + o) m → Exp (m + o) zero
applyToVars {m} {o} exp  = ((flip apply* ) (map Var (mkFinvec m o))) exp



evalApplyToVars :  ∀ {n : ℕ} (exp : Exp zero n) (vs : Vec ℕ n) → evalST (applyToVars (raiseExP n exp)) (fastReverse vs) [] ≡ evalST exp [] vs
evalApplyToVars  {n} exp vs  = 
    evalST (apply* (raiseExP n exp) (map Var (mkFinvec n zero))) (fastReverse vs) [] 
            ≡⟨ evalApply*Eq (raiseExP n exp)  (map Var (mkFinvec n zero)) (fastReverse vs) ⟩ 
    evalST (raiseExP n exp) (fastReverse vs) ((map (λ arg → evalST arg (fastReverse vs) []) ((map Var (mkFinvec n zero))))) 
            ≡⟨ evalApplyToVarsHelper1 vs (raiseExP n exp) ⟩ 
    (evalST (raiseExP n exp) (fastReverse vs) vs) 
            ≡⟨ sym( raiseExPSound exp [] (fastReverse vs) vs) ⟩ 
    (evalST exp [] vs) ∎ 


prToSt* : ∀ {m : ℕ} (o : ℕ)   → Vec (PR m) n → Vec (Exp (o) m) n
prToSt* o  [] = []
prToSt* {m} o  (x ∷ vs) = (prToST (o) x) ∷ (prToSt* o  vs)


generalComp : ∀ {n : ℕ} {m : ℕ}  → (Exp zero n) → (Vec (Exp zero m) n) → Exp zero m
generalComp {n} {m} f' gs' = prepLambdas' zero m (apply* (raiseExP m f') (map (applyToVars {m} {zero}) (map (raiseExP m)  gs')))



convComp {n} {m} f gs = generalComp (prToST' f) (prToSt* zero gs)




map-id : ∀ {A : Set} {n : ℕ} (vs : Vec A n) → map (λ x → x) vs ≡ vs
map-id [] = refl
map-id (x ∷ vs) = cong (x ∷_) (map-id vs)


cong3 : ∀ {A B C D : Set}(f : A → B → C → D) {x y u v w z} → x ≡ y → u ≡ v → w ≡ z → f x u w ≡ f y v z
cong3 f refl refl refl = refl


evalApplyToVarsFun :  ∀ {A : Set} {n : ℕ} (vs : Vec ℕ n) → (λ exp → evalST ((applyToVars {n} {zero}) (raiseExP n exp)) (fastReverse vs) []) ≗  (λ exp → evalST exp [] vs)
evalApplyToVarsFun  vs = λ exp → evalApplyToVars exp vs

evalApplyToVarsMap : ∀ {n m : ℕ} (vs : Vec ℕ n) (gs : Vec (Exp zero n) m) → map (λ exp → evalST ((applyToVars {n} {zero}) (raiseExP n exp)) (fastReverse vs) []) gs ≡ map (λ exp → evalST exp [] vs) gs
evalApplyToVarsMap vs [] = refl
evalApplyToVarsMap vs (g ∷ gs) rewrite evalApplyToVars g vs | evalApplyToVarsMap vs gs  = refl


evalGeneralCompHelper1 : ∀ {n m : ℕ} (args : Vec ℕ m)(f : Exp zero n) (gs : Vec (Exp zero m) n) → evalST (raiseExP m f) (fastReverse args)(map (λ arg → evalST arg (fastReverse args) []) (map (applyToVars {m} {zero}) (map (raiseExP m) gs))) ≡ evalST (raiseExP m f) (fastReverse args) (map (( λ arg → evalST arg (fastReverse args) []) ∘ (applyToVars {m} {zero})) ((map (raiseExP m) gs)))
evalGeneralCompHelper1 {n} {m} args f gs rewrite ∘-map (λ arg → evalST arg (fastReverse args) []) (applyToVars {m} {zero}) (map (raiseExP m) gs) = refl 

evalGeneralCompHelper2 : ∀ {n m : ℕ} (args : Vec ℕ m)(f : Exp zero n) (gs : Vec (Exp zero m) n) →  evalST (raiseExP m f) (fastReverse args) (map (λ x → evalST (applyToVars {m} {zero} x) (fastReverse args) []) (map (raiseExP m) gs)) ≡ evalST (raiseExP m f) (fastReverse args) (map (λ x → evalST (applyToVars {m} {zero} (raiseExP m x)) (fastReverse args) [])(gs))
evalGeneralCompHelper2 {n} {m} args f gs rewrite ∘-map (λ x → evalST (applyToVars {m} {zero} x) (fastReverse args) []) (raiseExP m) gs = refl

evalGeneralCompHelper3 : ∀ {m n} (f : Exp zero n) (args : Vec ℕ m)(gs : Vec (Exp zero m) n) → evalST (raiseExP m f) (fastReverse args)(map(λ x → evalST (applyToVars {m} {zero} (raiseExP m x)) (fastReverse args) []) gs) ≡ evalST (raiseExP m f) (fastReverse args)  (map(λ exp → evalST exp [] args) gs)
evalGeneralCompHelper3 f args gs rewrite evalApplyToVarsMap args gs = refl


evalGeneralComp : ∀ {n m : ℕ} (f : Exp zero n) (gs : Vec (Exp zero m) n) (args : Vec  ℕ m)  → evalSTClosed (generalComp f gs) args ≡ evalSTClosed f (map (λ g → evalSTClosed g args) gs)
evalGeneralComp {n} {m} f gs args = (evalSTClosed (generalComp f gs) args)
                                                ≡⟨⟩ evalSTClosed (prepLambdas' zero m (apply* (raiseExP m f) (map (applyToVars {m} {zero}) (map (raiseExP m)  gs)))) args 
                                                        ≡⟨ prepLambdasEvalClose {m} args ((apply* (raiseExP m f) (map (applyToVars {m} {zero}) (map (raiseExP m)  gs)))) ⟩ 
                                                 evalST (apply* (raiseExP m f) (map (applyToVars {m} {zero})(map (raiseExP {zero} {m} m ) gs))) (fastReverse args) [] 
                                                        ≡⟨ evalApply*Eq (raiseExP m f)  (map (applyToVars {m} {zero})  (map (raiseExP {zero} {m} m) gs)) (fastReverse args) ⟩ 
                                                evalST (raiseExP m f) (fastReverse args)(map (λ arg → evalST arg (fastReverse args) [])(map (applyToVars {m} {zero}) (map (raiseExP m) gs))) 
                                                        ≡⟨ evalGeneralCompHelper1 args f gs ⟩ 
                                                evalST (raiseExP m f) (fastReverse args) (map ((λ arg → evalST arg (fastReverse args) []) ∘ (applyToVars {m} {zero})) (map (raiseExP m) gs)) 
                                                        ≡⟨⟩ 
                                                evalST (raiseExP m f) (fastReverse args) (map (λ x → evalST ((applyToVars {m} {zero}) x) (fastReverse args) []) (map (raiseExP m) gs)) 
                                                        ≡⟨ evalGeneralCompHelper2 args f gs ⟩ 
                                                evalST (raiseExP m f) (fastReverse args) (map (λ x → evalST (applyToVars {m} {zero} (raiseExP m x)) (fastReverse args) []) gs) 
                                                        ≡⟨ evalGeneralCompHelper3 f args gs ⟩ 
                                                evalST (raiseExP m f) (fastReverse args) (map (λ exp → evalSTClosed exp args) gs) 
                                                        ≡⟨ sym ( raiseExPSound f []  (fastReverse args) (map (λ exp → evalSTClosed exp args) gs)) ⟩ 
                                                evalST f [] (map (λ exp → evalSTClosed exp args) gs) ∎ 



-- -- ------------------------------------------------------------------------------
-- -- -- embedding
-- -- ------------------------------------------------------------------------------

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



-- evalExp'' : ∀ {n : ℕ} {ctx : Ctx n} {ty : Ty}  → Exp' ctx ty → HVec evalTy ctx → HVec evalTy (getArgs ty) → ℕ
-- evalExp'' exp ctx = uncurryH (evalExp' exp ctx)

-- helper' : ∀ (m : ℕ ) → repeat (countArgs (ℕtoTy m)) TyNat ≡ getArgs (ℕtoTy m) 
-- helper' zero = refl
-- helper' (suc n) = cong (λ xs → TyNat ∷ xs) (helper' n)

-- helper''' : ∀ {m} → (countArgs (ℕtoTy m)) ≡ m 
-- helper''' {zero} = refl
-- helper''' {suc m} = cong suc (helper''' {m})


-- {-# REWRITE helper' helper''' #-}

-- helper3 : ∀ (n : ℕ) → repeat n TyNat ≡ getArgs (ℕtoTy n)
-- helper3 zero = refl
-- helper3 (suc n) = cong (λ vs → TyNat ∷ vs) (helper3 n)


-- {-# REWRITE helper3  #-}


-- convVarSound : ∀ {n : ℕ} (ctx : Vec ℕ n) (x : Fin n)  → lookup ctx x ≡ evalExp'' (Var' (finToDBI x)) (toHVec' ctx) ([]ᴴ)
-- convVarSound  (x ∷ ctx) zero = refl
-- convVarSound (x₁ ∷ ctx) (suc x) rewrite convVarSound  ctx x  = refl


-- --  
 
-- sound-embedd : ∀ {n m : ℕ} (exp : Exp n m)  (ctx : Vec ℕ n) (args : Vec ℕ m) → (evalST exp ctx args)  ≡  (evalExp'' (embedd  exp) (toHVec' ctx) ) ( (toHVec'   ( args)))
-- sound-embedd (Var x) ctx []   = convVarSound ctx x
-- sound-embedd {n} {suc m} (Lam exp) (ctx) (x ∷ args) rewrite sound-embedd exp (x ∷ ctx) args = refl
-- sound-embedd CZero ctx args = refl
-- sound-embedd Suc ctx [ n ] = refl 
-- sound-embedd (App f x) ctx args rewrite sound-embedd x ctx []  | sound-embedd f ctx ( (evalExp' (embedd x) (toHVec' ctx)) ∷ args) = refl
-- sound-embedd (Nat n) ctx [] = refl
             