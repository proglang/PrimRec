-- {-# OPTIONS --rewriting --prop -v rewriting:50 #-}
{-# OPTIONS --rewriting  #-}
{-# OPTIONS --allow-unsolved-metas #-}
module System-T where



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
    PRecT : Exp n 2 → Exp n zero → Exp n zero → Exp n zero

para : ∀ {A : Set} (h : A → ℕ → A) → A → ℕ → A
para h acc zero = acc
para h acc (suc counter) = h (para h acc counter) counter

evalST : ∀ {n m : ℕ} → Exp n m → Vec ℕ n → Vec ℕ m → ℕ 
evalST (Var x) ctx args = lookup ctx x
evalST (Lam exp) ctx (x ∷ args) = evalST exp (x ∷ ctx) args
evalST CZero ctx args = 0
evalST Suc ctx [ x ] = suc x
evalST (App f x) ctx args = evalST f ctx ( evalST x ctx [] ∷ args)
evalST (Nat n) _ [] = n
evalST (PRecT h acc counter) ctx [] = para (λ acc counter → (evalST h ctx) [ acc , counter ]) (evalST acc ctx []) (evalST counter ctx []) 




evalSTClosed : Exp zero m → Vec ℕ m → ℕ
evalSTClosed exp args = evalST exp [] args

raiseExP : ∀ {m n} (o) → Exp m n → Exp (m + o) n
raiseExP  {m} {n} o (Var x) =  Var (inject+ o  x   ) --rewrite +-comm m o 
raiseExP o (Lam exp) = Lam (raiseExP o exp)
raiseExP o CZero = CZero
raiseExP o Suc = Suc
raiseExP o (App f x) = App (raiseExP o f) (raiseExP o x)
raiseExP o (Nat x) = Nat x
raiseExP o ((PRecT h acc counter)) = PRecT (raiseExP o h) (raiseExP o acc) (raiseExP o counter)

raiseExp0Eq : ∀ {m n}  (exp : Exp m n) → raiseExP 0 exp ≡ exp 
raiseExp0Eq (Var x) = cong Var (inject+0 x)
raiseExp0Eq (Lam exp) = cong Lam (raiseExp0Eq exp)
raiseExp0Eq CZero = refl
raiseExp0Eq Suc = refl
raiseExp0Eq (App f x) rewrite raiseExp0Eq f |  raiseExp0Eq x = refl
raiseExp0Eq (Nat x) = refl
raiseExp0Eq ((PRecT h acc counter)) rewrite raiseExp0Eq h | raiseExp0Eq acc | raiseExp0Eq counter = refl

cong3 : ∀ {A B C D : Set} {x y u v w z} (f : A → B → C → D)  → x ≡ y → u ≡ v → w ≡ z → f x u w ≡ f y v z
cong3 f refl refl refl = refl

-- PLFA 
postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

ext2 : ∀ {A B C : Set} {f g : A → B → C}
        → (∀ (x : A) (y : B) → f x y ≡ g x y)
      -----------------------
        → f ≡ g
ext2  = λ x → extensionality (λ x₁ → extensionality (λ x₂ → x x₁ x₂))

raiseExPSound : ∀ {m n o} (exp : Exp m n) (ctx : Vec ℕ m)(ctx2 : Vec ℕ o)(args : Vec ℕ n) → evalST exp ctx args ≡ evalST (raiseExP o exp) (ctx ++ ctx2) args
raiseExPSound (Var x) (ctx) ctx2 args = sym (lookup-++ˡ ctx ctx2 x) -- lookup-++ˡ {! ctx  !} {!   !} x
raiseExPSound (Lam exp) ctx ctx2 (a ∷ args) rewrite raiseExPSound exp (a ∷ ctx) ctx2 args = refl
raiseExPSound CZero ctx ctx2 args = refl
raiseExPSound Suc ctx ctx2 [ x ] = refl
raiseExPSound {m}{n} {o} (App f x) ctx ctx2 args  rewrite raiseExPSound x ctx ctx2 []  | raiseExPSound f ctx ctx2  (evalST (raiseExP o x) (ctx ++ ctx2) [] ∷ args) = refl
raiseExPSound (Nat x) ctx ctx2 [] = refl
raiseExPSound (PRecT h acc counter) ctx ctx2 []  rewrite raiseExPSound acc ctx ctx2 [] |  raiseExPSound counter ctx ctx2 [] | ext2 λ x y → raiseExPSound h ctx ctx2 [ x , y ]  = refl 


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

convPR : ∀ {n} → PR n → PR (suc (suc n)) → Exp zero (suc n)



prToST' : ∀ {m : ℕ} → PR m → Exp zero m 
prToST'  {m} Z = mkConstZero m
prToST'  σ = Suc
prToST' (π i) = convProj ( i)
prToST' (C f gs) = convComp f gs 
prToST'  (P g h) = convPR g h

prToST : (n : ℕ)  → PR m → Exp n m 
prToST n pr = raiseExP n (prToST' pr)


convCompSound : ∀ {n m} (f : PR n)  (gs : Vec  (PR m) n ) (vs : Vec ℕ m) → evalSTClosed (convComp f gs) vs  ≡  eval f (eval* gs vs)

convParaSound : ∀ {n : ℕ} (g : PR n) (h : PR (suc (suc n))) (args : Vec ℕ (suc n) ) → evalSTClosed (prToST' (P g h)) args ≡ eval (P g h) args


eqPrSTn : ∀  {n : ℕ} ( pr : PR n) (v : Vec ℕ n ) → eval pr v ≡ evalSTClosed (prToST'   pr) v
eqPrSTn {n} Z v = sym (convZeroSound n v)
eqPrSTn  σ [ x ] = refl
eqPrSTn  {suc n} (π i) (vs) =  sym (convProjSound i vs)
eqPrSTn  (C f gs) vs = sym (convCompSound f gs vs)
eqPrSTn  (P g h) vs = sym (convParaSound g h vs)                


-- -- ------------------------------------------------------------------------------
-- -- -- composition
-- -- ------------------------------------------------------------------------------

mkFinvec : ∀ (n : ℕ ) (m : ℕ ) → Vec (Fin (n + m)) n
mkFinvec zero m = []
mkFinvec (suc n) m = inject+ m  (fromℕ n ) ∷ (mkFinvec n (suc m))

mkFinvec' : ∀ (n : ℕ ) (m : ℕ ) (o : ℕ) → Vec (Fin (o + n + m)) n
mkFinvec' n m o = map (raise o) (mkFinvec n m)

-- arity : ∀ {n : ℕ} (pr : PR n) → ℕ
-- arity {n} _ = n

apply* : ∀ {n m o : ℕ} → Exp m (n + o) → Vec (Exp m zero) o  → Exp m n
apply* exp [] = exp
apply* exp (x ∷ vec) = apply* (App exp x) vec


evalApply*Eq :  ∀ {n m : ℕ} (exp : Exp n m) (args : Vec (Exp n zero) m) (ctx : Vec ℕ n) → evalST (apply* exp args) ctx  [] ≡ evalST exp  ctx (map (λ arg → evalST arg ctx []) args)
evalApply*Eq exp [] ctx = refl
evalApply*Eq {n} {suc m } exp (arg ∷ args) ctx rewrite evalApply*Eq {n} {m} (App exp arg) args ctx = refl

maplookupEq :  {n m : ℕ}  (vs : Vec ℕ n) (ys : Vec ℕ m) → (map (λ x → lookup (vs ++r ys) x) (mkFinvec n m)) ≡ vs
maplookupEq {.zero} [] ys = refl
maplookupEq {(suc n)} {m} (x ∷ vs) ys rewrite lookupOP' zero  (x ∷ vs) ys = cong (λ vec → x ∷ vec) (maplookupEq {n} {suc m} vs (x ∷ ys)) 

maplookupEq3 :  {o n m  : ℕ}  (zs : Vec ℕ o) (xs : Vec ℕ n) (ys : Vec ℕ m) → (map (λ x → lookup (zs ++ xs ++r ys) x) (mkFinvec' n m o)) ≡ xs
maplookupEq3 zs [] ys  = refl
maplookupEq3 {o} {suc n} {m}  zs (x ∷ xs) ys   rewrite lookup-++ʳ zs (xs ++r (x ∷ ys))  (inject+ m (fromℕ n)) | lookupOP' zero  (x ∷ xs) ys = cong (λ vec → x ∷ vec) (maplookupEq3  zs xs (x ∷ ys) )



mapEvalVarsEq2 : ∀ {n m : ℕ} (xs : Vec ℕ n) (ys : Vec ℕ m) →  (map (λ arg → evalST arg (xs ++r ys) []) (map Var (mkFinvec n m))) ≡ xs 
mapEvalVarsEq2 {n} {m} xs ys    = map (λ arg → evalST arg (xs ++r ys) []) (map Var (mkFinvec n m)) 
                                        ≡⟨ ∘-map (λ arg → evalST arg (xs ++r ys) []) Var (mkFinvec n m) ⟩ 
                                map ((λ arg → evalST arg (xs ++r ys) []) ∘ Var) (mkFinvec n m) 
                                        ≡⟨⟩ 
                                map (λ f → lookup (xs ++r ys) f) (mkFinvec n m) 
                                        ≡⟨ maplookupEq xs ys ⟩ 
                                xs ∎

mapEvalVarsEq3 : ∀ {o n m : ℕ} (zs : Vec ℕ o) (xs : Vec ℕ n) (ys : Vec ℕ m) →  (map (λ arg → evalST arg (zs ++ xs ++r ys) []) (map Var (mkFinvec' n m o))) ≡ xs 
mapEvalVarsEq3  {o} {n} {m}  zs xs ys  = map (λ arg → evalST arg (zs ++ xs ++r ys) []) (map Var (mkFinvec' n m o)) 
                                        ≡⟨ ∘-map (λ arg → evalST arg (zs ++ xs ++r ys) []) Var (mkFinvec' n m o) ⟩ 
                                map ((λ arg → evalST arg (zs ++ xs ++r ys) []) ∘ Var) (mkFinvec' n m o) 
                                        ≡⟨⟩ 
                                map (λ f → lookup (zs ++ xs ++r ys) f) (mkFinvec' n m o) 
                                        ≡⟨ maplookupEq3 zs xs ys ⟩ 
                                xs ∎



evalApplyToVars2Helper1 : ∀ {n m : ℕ} (xs : Vec ℕ n) (ys : Vec ℕ m) (exp : Exp zero n) → evalST (raiseExP (n + m) exp) (xs ++r ys)(map (λ arg → evalST arg (xs ++r ys) []) (map Var (mkFinvec n m)))  ≡ evalST (raiseExP (n + m) exp) (xs ++r ys) xs
evalApplyToVars2Helper1 xs ys exp rewrite mapEvalVarsEq2 xs ys = refl


evalApplyToVars3Helper1 :   ∀ {n m o : ℕ} (xs : Vec ℕ n) (ys : Vec ℕ m) (zs : Vec ℕ o) (exp : Exp (n + (m + o)) m) →  evalST exp (xs ++ ys ++r zs)(map (λ arg → evalST arg (xs ++ ys ++r zs) [])(map Var (mkFinvec' m o n))) ≡ evalST exp (xs ++ ys ++r zs) ys
evalApplyToVars3Helper1 xs ys zs exp rewrite mapEvalVarsEq3 xs ys zs = refl

applyToVars : ∀ {m o} → Exp (m + o) m → Exp (m + o) zero
applyToVars {m} {o} exp  = ((flip apply* ) (map Var (mkFinvec m o))) exp


-- ∀ (n : ℕ ) (m : ℕ ) (o : ℕ) → Vec (Fin (o + n + m)) n
 -- length inject raise

applyToVars3 : ∀ {n m o} → Exp (n + m + o) m → Exp (n + m + o) zero
applyToVars3 {n}{m} {o} exp  = ((flip apply* ) (map Var (mkFinvec' m o n)))  exp

-- raise - length - inject

evalApplyToVars2 :  ∀ {n m : ℕ} (exp : Exp zero n) (xs : Vec ℕ n) (ys  : Vec ℕ m) → evalST (applyToVars {n} {m} (raiseExP (n + m) exp)) (xs ++r ys) [] ≡ evalST exp [] xs
evalApplyToVars2  {n} {m} exp xs ys  = 
        evalST (applyToVars (raiseExP (n + m) exp)) (xs ++r ys) [] 
                ≡⟨ evalApply*Eq (raiseExP (n + m) exp)  (map Var (mkFinvec n m)) (xs ++r ys) ⟩ 
        evalST (raiseExP (n + m) exp) (xs ++r ys) (map (λ arg → evalST arg (xs ++r ys) []) (map Var (mkFinvec n m))) 
                ≡⟨ evalApplyToVars2Helper1 xs ys exp ⟩ 
        evalST (raiseExP (n + m) exp) (xs ++r ys) xs 
                ≡⟨ sym( raiseExPSound exp [] (xs ++r ys) xs) ⟩ 
        (evalST exp [] xs) ∎ 


evalApplyToVars3 :  ∀ {n m o : ℕ} (exp : Exp ( n + m + o) m ) (zs : Vec ℕ (o))(xs : Vec ℕ n) (ys  : Vec ℕ m) → evalST (applyToVars3 {n} {m} {o} (exp)) ( xs ++ ys ++r zs) [] ≡ evalST exp ( xs ++ ys ++r zs) ys
evalApplyToVars3  {n} {m} {o} exp zs xs ys  = 
        (evalST (applyToVars3 exp) (xs ++ ys ++r zs) [] ) 
                ≡⟨ evalApply*Eq (exp)  (map Var (mkFinvec' m o n)) (xs ++ ys ++r zs )⟩ 
        evalST exp (xs ++ ys ++r zs)(map (λ arg → evalST arg (xs ++ ys ++r zs) [])(map Var (mkFinvec' m o n)))
                ≡⟨ evalApplyToVars3Helper1 xs ys zs exp ⟩ 
        (evalST exp (xs ++ (ys ++r zs)) ys) ∎ 





evalApplyToVars :  ∀ {n : ℕ} (exp : Exp zero n) (vs : Vec ℕ n) → evalST (applyToVars (raiseExP n exp)) (fastReverse vs) [] ≡ evalST exp [] vs
evalApplyToVars  {n} exp vs  = evalApplyToVars2 exp vs []


prToSt* : ∀ {m : ℕ} (o : ℕ)   → Vec (PR m) n → Vec (Exp (o) m) n
prToSt* o  [] = []
prToSt* {m} o  (x ∷ vs) = (prToST (o) x) ∷ (prToSt* o  vs)


generalComp : ∀ {n : ℕ} {m : ℕ}  → (Exp zero n) → (Vec (Exp zero m) n) → Exp zero m
generalComp {n} {m} f' gs' = prepLambdas' zero m (apply* (raiseExP m f') (map (applyToVars {m} {zero}) (map (raiseExP m)  gs')))



convComp {n} {m} f gs = generalComp (prToST' f) (prToSt* zero gs)




map-id : ∀ {A : Set} {n : ℕ} (vs : Vec A n) → map (λ x → x) vs ≡ vs
map-id [] = refl
map-id (x ∷ vs) = cong (x ∷_) (map-id vs)





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


eval*≡evalPrToST* : ∀ {n m}  (vs : Vec ℕ m) (gs : Vec (PR m) n) → (map (λ g → evalSTClosed g vs) (prToSt* zero gs)) ≡ (eval* gs vs)
eval*≡evalPrToST* vs [] = refl
eval*≡evalPrToST* vs (g ∷ gs) rewrite eqPrSTn  g vs | eval*≡evalPrToST* vs gs | raiseExp0Eq (prToST' g) = refl

convCompSoundHelper : ∀ {n m} (f : PR n) (vs : Vec ℕ m) (gs : Vec (PR m) n) → evalSTClosed (prToST' f) (map (λ g → evalSTClosed g vs) (prToSt* zero gs))≡ eval f (eval* gs vs)
convCompSoundHelper f vs gs rewrite eval*≡evalPrToST* vs gs | eqPrSTn f (eval* gs vs) = refl

convCompSound f gs vs = (evalSTClosed (convComp f gs) vs) 
        ≡⟨⟩ 
                (((evalSTClosed (generalComp (prToST' f) (prToSt* zero gs)) vs)) 
        ≡⟨ evalGeneralComp (prToST' f) (prToSt* zero gs) vs ⟩ 
                (evalSTClosed (prToST' f)  (map (λ g → evalSTClosed g vs) (prToSt* zero gs)) 
        ≡⟨ convCompSoundHelper f  vs gs ⟩ 
                (eval f (eval* gs vs)) ∎ ))


-- -- ------------------------------------------------------------------------------
-- -- -- primitive recursion
-- -- ------------------------------------------------------------------------------

paraNat : ∀ {n} → (Vec ℕ n → ℕ) → (Vec ℕ (suc (suc n)) → ℕ) → Vec ℕ ( (suc n)) → ℕ
paraNat g h (zero ∷ args) = g args
paraNat g h (suc x ∷ args) = h (paraNat g h (x ∷ args) ∷ (x ∷ args))

paraNat' : ∀ {n} → (Vec ℕ n → ℕ) → (Vec ℕ (suc (suc n)) → ℕ) → Vec ℕ ( (suc n)) → ℕ
paraNat' g h (x ∷ args) = para (λ acc n → h (acc ∷ (n ∷ args))) (g args) x

paraNatEq : ∀ {n} → (g : Vec ℕ n → ℕ) → (h : Vec ℕ (suc (suc n)) → ℕ) → (args : Vec ℕ ( (suc n))) → paraNat g h args ≡ paraNat' g h args
paraNatEq g h (zero ∷ args) = refl
paraNatEq g h (suc x ∷ args) rewrite paraNatEq  g h (x ∷ args)  = refl

paraNatPR : ∀ {n : ℕ} (g : PR n) (h : PR (suc (suc n))) (vs : Vec ℕ (suc n) ) → eval (P g h) vs ≡ paraNat (eval g) (eval h) vs
paraNatPR g h (zero ∷ vs) = refl
paraNatPR g h (suc x ∷ vs) rewrite paraNatPR  g h (x ∷ vs)  = refl 


paraT : ∀ {n} → Exp zero n → Exp zero (suc (suc n)) →  Exp zero ( (suc n))
paraT {n} g h = prepLambdas' 0 (suc n)  (PRecT 
                ---(Lam (Lam (applyToVars {n} {3} (App (App (raiseExP  (n + 3) h) (Var (suc zero))) (Var zero))))) 
                (Lam (Lam (applyToVars3 {2} {n} {1} (App (App (raiseExP  (n + 3) h) (Var (suc zero))) (Var zero))))) 
                --(Lam (Lam (applyToVars {n} {3}    (raiseExP (suc n) (App (App (raiseExP  (2) h) (Var (suc zero))) (Var zero)) )          ))) 
                ((applyToVars {n} {1} (raiseExP (suc n) g)) )
                (Var (fromℕ n))) 


convPR g h = paraT ((prToST'  g )) (prToST'  h)


-- applyToVars3 : ∀ {n m o} → Exp (n + m + o) m → Exp (n + m + o) zero
-- applyToVars3 {n}{m} {o} exp  = ((flip apply* ) (map Var (mkFinvec' m o n)))  exp

-- -- raise - length - inject


evalParaTHelper1 : ∀  {n x} (args : Vec ℕ n ) → (lookup (fastReverse (x ∷ args)) (fromℕ n)) ≡ x
evalParaTHelper1 {n} {x} args = lookupOpRev zero (x ∷ args)


evalParaTHelper2 :  ∀  {n x  : ℕ} (args : Vec ℕ n ) (g : Exp zero n) → (evalST (applyToVars  { n} {1} (raiseExP (suc n) g)) (fastReverse (x ∷ args)) []) ≡ evalSTClosed g args
evalParaTHelper2  {n} {x} args g = evalApplyToVars2 g args [ x ] 


evalParaTHelper4 : ∀  {n} (x : ℕ) (counter : ℕ) (acc : ℕ) (h : Exp zero (suc (suc n))) (args : Vec ℕ n) → evalST (applyToVars3 {2} {n} {1} (App (App (raiseExP (suc (suc (suc n))) h) (Var (suc zero)))(Var zero))) (counter ∷ acc ∷ fastReverse (x ∷ args)) [] ≡ evalSTClosed h (acc ∷ counter ∷ args)
evalParaTHelper4 {n} x counter acc h args =     evalST (applyToVars3 {2} {n} {1} (App (App (raiseExP (suc (suc (suc n))) h) (Var (suc zero)))(Var zero)))  (counter ∷ acc ∷ fastReverse (x ∷ args)) [] 
                                                        ≡⟨ evalApplyToVars3 (App (App (raiseExP (suc (suc (suc n))) h) (Var (suc zero))) (Var zero)) [ x ] [ counter , acc ] args ⟩ 
                                                evalST (raiseExP (suc (suc (suc n))) h) (counter ∷ acc ∷ (args ++r [ x ])) (acc ∷ counter ∷ args) 
                                                        ≡⟨ sym (raiseExPSound h [] (counter ∷ acc ∷ (args ++r [ x ]))  (acc ∷ counter ∷ args))  ⟩ (evalSTClosed h (acc ∷ counter ∷ args)) ∎ 

evalParaTHelper3 : ∀  {n x : ℕ} (h : Exp zero (suc (suc n))) (args : Vec ℕ n) → (λ acc counter →
         evalST
         (applyToVars3 {2} {n} {1}
          (App (App (raiseExP (suc (suc (suc n))) h) (Var (suc zero)))
           (Var zero)))
         (counter ∷ acc ∷ fastReverse (x ∷ args)) []) ≡ 
         (λ acc counter  → evalSTClosed h (acc ∷ (counter ∷ args)))
evalParaTHelper3 {n} {x} h args = ext2 (λ acc counter → evalParaTHelper4 x counter acc h args)


evalParaTHelper5 : ∀  {n x : ℕ} (g : Exp zero ( ( n))) (h : Exp zero (suc (suc n))) (args : Vec ℕ n)
        → para
      (λ acc counter →
         evalST
         (applyToVars3 {2} {n} {1}
          (App (App (raiseExP (suc (suc (suc n))) h) (Var (suc zero)))
           (Var zero)))
         (counter ∷ acc ∷ fastReverse (x ∷ args)) [])
      (evalST (applyToVars  { n} {1}  (raiseExP (suc n) g)) (fastReverse (x ∷ args))
       [])
      (lookup (fastReverse (x ∷ args)) (fromℕ n))
      ≡
      para (λ acc counter → evalSTClosed h (acc ∷ counter ∷ args))
      (evalSTClosed g args) x
evalParaTHelper5 {n} {x} g h args rewrite evalParaTHelper1 {n} {x} args | evalParaTHelper2  {n} {x} args g | evalParaTHelper3 {n} {x} h args = refl


evalParaT : ∀ {n x : ℕ} (g : Exp zero n) (h : Exp zero (suc (suc n))) (args : Vec ℕ n ) → evalSTClosed (paraT g h) (x ∷ args) ≡ para (λ acc counter  → evalSTClosed h (acc ∷ (counter ∷ args))) (evalSTClosed g args) x  
evalParaT {n} {x} g h args = (evalSTClosed (paraT g h) (x ∷ args)) 
                        ≡⟨⟩ 
                ((evalSTClosed (prepLambdas' 0 (suc n)  (PRecT 
                (Lam (Lam (applyToVars3 {2} {n} {1} (App (App (raiseExP  (n + 3) h) (Var (suc zero))) (Var zero))))) 
                ( (applyToVars {n} {1} (raiseExP (suc n) g)) )
                (Var (fromℕ n))) ) (x ∷ args)) 
                        
                        ≡⟨ prepLambdasEvalClose (x ∷ args) (PRecT 
                        (Lam (Lam (applyToVars3 {2} {n} {1} (App (App (raiseExP  (n + 3) h) (Var (suc zero))) (Var zero))))) 
                        ( (applyToVars { n} {1} (raiseExP (suc n) g)) )
                        (Var (fromℕ n))) ⟩ 
        
                para(λ acc counter → evalST (applyToVars3 (App (App (raiseExP (suc (suc (suc n))) h) (Var (suc zero)))(Var zero)))(counter ∷ acc ∷ fastReverse (x ∷ args)) [])(evalST (applyToVars (raiseExP (suc n) g)) (fastReverse (x ∷ args))[]) (lookup (fastReverse (x ∷ args)) (fromℕ n)) 
                        
                        ≡⟨ evalParaTHelper5 {n}  {x} g h args ⟩ 
                
                (para (λ acc counter → evalSTClosed h (acc ∷ counter ∷ args)) (evalSTClosed g args) x) ∎)


convParaSound g h (x ∷ args) = (evalSTClosed (prToST' (P g h)) (x ∷ args))
                                ≡⟨⟩ 
                        evalSTClosed (paraT ((prToST'  g )) (prToST'  h)) (x ∷ args) 
                                ≡⟨ evalParaT (prToST'  g ) (prToST'  h) args ⟩ 
                        para (λ acc counter → evalSTClosed (prToST' h) (acc ∷ counter ∷ args)) (evalSTClosed (prToST' g) args) x 
                                ≡⟨⟩ 
                        paraNat' (evalSTClosed (prToST' g)) (evalSTClosed (prToST' h)) ((x ∷ args)) 
                                ≡⟨ sym (paraNatEq (evalSTClosed (prToST' g)) (evalSTClosed (prToST' h) ) ((x ∷ args))) ⟩ 
                        paraNat (evalSTClosed (prToST' g)) (evalSTClosed (prToST' h))(x ∷ args) 
                                ≡⟨ cong3 { w = x ∷ args } paraNat (extensionality (λ v → sym (eqPrSTn g v))) ((extensionality (λ v → sym (eqPrSTn h v)))) refl  ⟩ 
                        paraNat (λ z → eval g z) (λ z → eval h z) (x ∷ args) 
                                ≡⟨⟩ 
                        paraNat (eval g) (eval h) (x ∷ args) 
                                ≡⟨ sym ( paraNatPR g h  (x ∷ args)) ⟩ 
                        eval (P g h) (x ∷ args) ∎


-- paraNatPR : ∀ {n : ℕ} (g : PR n) (h : PR (suc (suc n))) (vs : Vec ℕ (suc n) ) → eval (P g h) vs ≡ paraNat (eval g) (eval h) vs
