-- {-# OPTIONS --rewriting --prop -v rewriting:50 #-}
{-# OPTIONS --rewriting  #-}
{-# OPTIONS --allow-unsolved-metas #-}
module System-T0 where



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

-- open import PR-Nat
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



prepLambdas : ∀ {o} (n : ℕ) → (m : ℕ) →  Exp (m + n) o -> Exp n (o + m)
prepLambdas {o} n zero exp   = exp
prepLambdas {o} n (suc m) exp   = Lam (prepLambdas  (suc n) m exp)


prepLambdasEval : ∀ {ctxLen argsLen : ℕ} (ctx : Vec ℕ ctxLen ) (args : Vec ℕ argsLen ) (exp) → evalST (prepLambdas ctxLen argsLen exp) ctx args ≡ evalST exp (args ++r ctx) []
prepLambdasEval ctx [] exp = refl
prepLambdasEval ctx (x ∷ args) exp = prepLambdasEval ((x ∷ ctx)) args  exp

prepLambdasEvalClose : ∀ {argsLen : ℕ}  (args : Vec ℕ argsLen ) (exp : Exp argsLen zero) → evalSTClosed (prepLambdas 0 argsLen exp) args ≡ evalST exp (fastReverse args) []
prepLambdasEvalClose = prepLambdasEval []


------------------------------------------------------------------------------
-- constant zero-function
------------------------------------------------------------------------------

mkConstZero :   (m : ℕ) → Exp zero m 
mkConstZero m = prepLambdas zero m CZero


evalMkConstZero : ∀  (n : ℕ ) (v : Vec ℕ n ) → evalSTClosed (mkConstZero n) v  ≡ 0
evalMkConstZero n v = prepLambdasEvalClose v CZero 

------------------------------------------------------------------------------
-- projection
------------------------------------------------------------------------------


mkProj : ∀ {m} → Fin (m)  →  Exp zero m
mkProj {m} f  = prepLambdas zero m (Var (opposite {m} f))

-- {-# REWRITE inject+0  #-}


evalMkProjHelper : ∀  {m : ℕ} (f : Fin (suc m ) ) (args : Vec ℕ (suc m))  → evalSTClosed (mkProj f)  args ≡ lookup (( fastReverse args) ) (opposite f)
evalMkProjHelper f args = prepLambdasEvalClose args (Var (opposite f))


evalMkProj : ∀  {n : ℕ} (f : Fin ((suc n)) ) (args : Vec ℕ (suc n))  → evalSTClosed (mkProj  (f)) args ≡ lookup args f
evalMkProj {n} f vs = evalST (mkProj  ( f)) [] vs 
    ≡⟨ evalMkProjHelper (f) vs ⟩ 
                        lookup (fastReverse vs) (opposite f) 
    ≡⟨ lookupOpRev f vs ⟩ 
                        (lookup vs f) ∎ 

-- -- ------------------------------------------------------------------------------
-- -- -- composition
-- -- ------------------------------------------------------------------------------


mkFinvec'' : ∀ (n : ℕ ) (m : ℕ ) → Vec (Fin (n + m)) n
mkFinvec'' zero m = []
mkFinvec'' (suc n) m = inject+ m  (fromℕ n ) ∷ (mkFinvec'' n (suc m))

mkFinvec' : ∀ (n : ℕ ) (m : ℕ ) (o : ℕ) → Vec (Fin (o + n + m)) n
mkFinvec' n m o = map (raise o) (mkFinvec'' n m)

mkFinvec : ∀ (n : ℕ ) (m : ℕ ) → Vec (Fin (n + m)) n
mkFinvec n m = mkFinvec' n m zero

apply* : ∀ {n m o : ℕ} → Exp m (n + o) → Vec (Exp m zero) o  → Exp m n
apply* exp [] = exp
apply* exp (x ∷ vec) = apply* (App exp x) vec


evalApply*Eq :  ∀ {n m : ℕ} (exp : Exp n m) (args : Vec (Exp n zero) m) (ctx : Vec ℕ n) → evalST (apply* exp args) ctx  [] ≡ evalST exp  ctx (map (λ arg → evalST arg ctx []) args)
evalApply*Eq exp [] ctx = refl
evalApply*Eq {n} {suc m } exp (arg ∷ args) ctx rewrite evalApply*Eq {n} {m} (App exp arg) args ctx = refl


maplookupEq :  {o n m  : ℕ}  (zs : Vec ℕ o) (xs : Vec ℕ n) (ys : Vec ℕ m) → (map (λ x → lookup (zs ++ xs ++r ys) x) (mkFinvec' n m o)) ≡ xs
maplookupEq zs [] ys  = refl
maplookupEq {o} {suc n} {m}  zs (x ∷ xs) ys   rewrite lookup-++ʳ zs (xs ++r (x ∷ ys))  (inject+ m (fromℕ n)) | lookupOP' zero  (x ∷ xs) ys = cong (λ vec → x ∷ vec) (maplookupEq  zs xs (x ∷ ys) )


mapEvalVarsEq : ∀ {o n m : ℕ} (zs : Vec ℕ o) (xs : Vec ℕ n) (ys : Vec ℕ m) →  (map (λ arg → evalST arg (zs ++ xs ++r ys) []) (map Var (mkFinvec' n m o))) ≡ xs 
mapEvalVarsEq  {o} {n} {m}  zs xs ys  = map (λ arg → evalST arg (zs ++ xs ++r ys) []) (map Var (mkFinvec' n m o)) 
                                        ≡⟨ ∘-map (λ arg → evalST arg (zs ++ xs ++r ys) []) Var (mkFinvec' n m o) ⟩ 
                                map ((λ arg → evalST arg (zs ++ xs ++r ys) []) ∘ Var) (mkFinvec' n m o) 
                                        ≡⟨⟩ 
                                map (λ f → lookup (zs ++ xs ++r ys) f) (mkFinvec' n m o) 
                                        ≡⟨ maplookupEq zs xs ys ⟩ 
                                xs ∎



evalApplyToVars'Helper1 :   ∀ {n m o : ℕ} (xs : Vec ℕ n) (ys : Vec ℕ m) (zs : Vec ℕ o) (exp : Exp (n + (m + o)) m) →  evalST exp (xs ++ ys ++r zs)(map (λ arg → evalST arg (xs ++ ys ++r zs) [])(map Var (mkFinvec' m o n))) ≡ evalST exp (xs ++ ys ++r zs) ys
evalApplyToVars'Helper1 xs ys zs exp rewrite mapEvalVarsEq xs ys zs = refl


-- ∀ (n : ℕ ) (m : ℕ ) (o : ℕ) → Vec (Fin (o + n + m)) n
 -- length inject raise

applyToVars' : ∀ {n m o} → Exp (n + m + o) m → Exp (n + m + o) zero
applyToVars' {n}{m} {o} exp  = ((flip apply* ) (map Var (mkFinvec' m o n)))  exp

applyToVars : ∀ {m o} → Exp (m + o) m → Exp (m + o) zero
applyToVars {m} {o} exp  = applyToVars' {zero} {m} {o} exp



-- raise - length - inject


evalApplyToVars' :  ∀ {n m o : ℕ} (exp : Exp ( n + m + o) m ) (zs : Vec ℕ (o))(xs : Vec ℕ n) (ys  : Vec ℕ m) → evalST (applyToVars' {n} {m} {o} (exp)) ( xs ++ ys ++r zs) [] ≡ evalST exp ( xs ++ ys ++r zs) ys
evalApplyToVars'  {n} {m} {o} exp zs xs ys  = 
        (evalST (applyToVars' exp) (xs ++ ys ++r zs) [] ) 
                ≡⟨ evalApply*Eq (exp)  (map Var (mkFinvec' m o n)) (xs ++ ys ++r zs )⟩ 
        evalST exp (xs ++ ys ++r zs)(map (λ arg → evalST arg (xs ++ ys ++r zs) [])(map Var (mkFinvec' m o n)))
                ≡⟨ evalApplyToVars'Helper1 xs ys zs exp ⟩ 
        (evalST exp (xs ++ (ys ++r zs)) ys) ∎ 

evalApplyToVars'' :  ∀ {n m : ℕ} (exp : Exp zero n) (xs : Vec ℕ n) (ys  : Vec ℕ m) → evalST (applyToVars {n} {m} (raiseExP (n + m) exp)) (xs ++r ys) [] ≡ evalST exp [] xs
evalApplyToVars''  {n} {m} exp xs ys  = 
        evalST (applyToVars (raiseExP (n + m) exp)) (xs ++r ys) [] 
                        ≡⟨ evalApplyToVars' (raiseExP (n + m) exp)  ys [] xs  ⟩ 
        (evalST (raiseExP (n + m) exp) ([] ++ (xs ++r ys)) xs) 
                        ≡⟨ sym (raiseExPSound exp [] ([] ++ (xs ++r ys)) xs) ⟩ (evalST exp [] xs) ∎



evalApplyToVars :  ∀ {n : ℕ} (exp : Exp zero n) (vs : Vec ℕ n) → evalST (applyToVars (raiseExP n exp)) (fastReverse vs) [] ≡ evalST exp [] vs
evalApplyToVars  {n} exp vs  = evalApplyToVars'' exp vs []




generalComp : ∀ {n : ℕ} {m : ℕ}  → (Exp zero n) → (Vec (Exp zero m) n) → Exp zero m
generalComp {n} {m} f' gs' = prepLambdas zero m (apply* (raiseExP m f') (map (applyToVars {m} {zero}) (map (raiseExP m)  gs')))








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
                                                ≡⟨⟩ evalSTClosed (prepLambdas zero m (apply* (raiseExP m f) (map (applyToVars {m} {zero}) (map (raiseExP m)  gs)))) args 
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



paraT : ∀ {n} → Exp zero n → Exp zero (suc (suc n)) →  Exp zero ( (suc n))
paraT {n} g h = prepLambdas 0 (suc n)  (PRecT 
                (Lam (Lam (applyToVars' {2} {n} {1} (App (App (raiseExP  (n + 3) h) (Var (suc zero))) (Var zero))))) 
                ((applyToVars {n} {1} (raiseExP (suc n) g)) )
                (Var (fromℕ n))) 




evalParaTHelper1 : ∀  {n x} (args : Vec ℕ n ) → (lookup (fastReverse (x ∷ args)) (fromℕ n)) ≡ x
evalParaTHelper1 {n} {x} args = lookupOpRev zero (x ∷ args)


evalParaTHelper2 :  ∀  {n x  : ℕ} (args : Vec ℕ n ) (g : Exp zero n) → (evalST (applyToVars  { n} {1} (raiseExP (suc n) g)) (fastReverse (x ∷ args)) []) ≡ evalSTClosed g args
evalParaTHelper2  {n} {x} args g = evalApplyToVars'' g args [ x ] 


evalParaTHelper4 : ∀  {n} (x : ℕ) (counter : ℕ) (acc : ℕ) (h : Exp zero (suc (suc n))) (args : Vec ℕ n) → evalST (applyToVars' {2} {n} {1} (App (App (raiseExP (suc (suc (suc n))) h) (Var (suc zero)))(Var zero))) (counter ∷ acc ∷ fastReverse (x ∷ args)) [] ≡ evalSTClosed h (acc ∷ counter ∷ args)
evalParaTHelper4 {n} x counter acc h args =     evalST (applyToVars' {2} {n} {1} (App (App (raiseExP (suc (suc (suc n))) h) (Var (suc zero)))(Var zero)))  (counter ∷ acc ∷ fastReverse (x ∷ args)) [] 
                                                        ≡⟨ evalApplyToVars' (App (App (raiseExP (suc (suc (suc n))) h) (Var (suc zero))) (Var zero)) [ x ] [ counter , acc ] args ⟩ 
                                                evalST (raiseExP (suc (suc (suc n))) h) (counter ∷ acc ∷ (args ++r [ x ])) (acc ∷ counter ∷ args) 
                                                        ≡⟨ sym (raiseExPSound h [] (counter ∷ acc ∷ (args ++r [ x ]))  (acc ∷ counter ∷ args))  ⟩ (evalSTClosed h (acc ∷ counter ∷ args)) ∎ 

evalParaTHelper3 : ∀  {n x : ℕ} (h : Exp zero (suc (suc n))) (args : Vec ℕ n) → (λ acc counter →
         evalST
         (applyToVars' {2} {n} {1}
          (App (App (raiseExP (suc (suc (suc n))) h) (Var (suc zero)))
           (Var zero)))
         (counter ∷ acc ∷ fastReverse (x ∷ args)) []) ≡ 
         (λ acc counter  → evalSTClosed h (acc ∷ (counter ∷ args)))
evalParaTHelper3 {n} {x} h args = ext2 (λ acc counter → evalParaTHelper4 x counter acc h args)


evalParaTHelper5 : ∀  {n x : ℕ} (g : Exp zero ( ( n))) (h : Exp zero (suc (suc n))) (args : Vec ℕ n)
        → para
      (λ acc counter →
         evalST
         (applyToVars' {2} {n} {1}
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
                ((evalSTClosed (prepLambdas 0 (suc n)  (PRecT 
                (Lam (Lam (applyToVars' {2} {n} {1} (App (App (raiseExP  (n + 3) h) (Var (suc zero))) (Var zero))))) 
                ( (applyToVars {n} {1} (raiseExP (suc n) g)) )
                (Var (fromℕ n))) ) (x ∷ args)) 
                        
                        ≡⟨ prepLambdasEvalClose (x ∷ args) (PRecT 
                        (Lam (Lam (applyToVars' {2} {n} {1} (App (App (raiseExP  (n + 3) h) (Var (suc zero))) (Var zero))))) 
                        ( (applyToVars { n} {1} (raiseExP (suc n) g)) )
                        (Var (fromℕ n))) ⟩ 
        
                para(λ acc counter → evalST (applyToVars' (App (App (raiseExP (suc (suc (suc n))) h) (Var (suc zero)))(Var zero)))(counter ∷ acc ∷ fastReverse (x ∷ args)) [])(evalST (applyToVars (raiseExP (suc n) g)) (fastReverse (x ∷ args))[]) (lookup (fastReverse (x ∷ args)) (fromℕ n)) 
                        
                        ≡⟨ evalParaTHelper5 {n}  {x} g h args ⟩ 
                
                (para (λ acc counter → evalSTClosed h (acc ∷ counter ∷ args)) (evalSTClosed g args) x) ∎)

