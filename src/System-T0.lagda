\begin{code}[hide]
{-# OPTIONS --rewriting  #-}
module System-T0 where

open import Data.Fin using (Fin; suc; zero; fromℕ; opposite; raise; inject+)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map)
open import Data.Vec.Properties using (lookup-++ˡ; map-cong; lookup-++ʳ)
open import Function.Base using (id; _∘_; flip)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; _≗_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Equality.Rewrite
open import FinProperties using (inject+0)
open import VecProperties using (_++r_; fastReverse; _ᴿ; lookupOpRev; lkupfromN)
open import EvalPConstructor using (para)


open import Utils


\end{code}

\newcommand{\defSTZero}{%
\begin{code}
data Exp n : ℕ → Set where
    Var : Fin n → Exp n zero
    Lam : Exp (suc n) m → Exp n (suc m)
    CZero :  Exp n zero
    Suc : Exp n (suc zero)
    App : Exp n (suc m) → Exp n (zero) → Exp n m
    Nat : ℕ → Exp n zero
    PRecT : Exp n 2 → Exp n zero → Exp n zero → Exp n zero
\end{code}}

\newcommand{\evalST}{%
\begin{code}
eval : Exp n m → Vec ℕ n → Vec ℕ m → ℕ 
eval (Var x) ctx _ = lookup ctx x
eval (Lam e) ctx (x ∷ args) = eval e (x ∷ ctx) args
eval CZero _ _ = 0
eval Suc _ [ x ] = suc x
eval (App f e) ctx args = eval f ctx ( eval e ctx [] ∷ args)
eval (Nat n) _ [] = n
eval (PRecT h e₀ en) ctx [] = para (λ acc counter → (eval h ctx) [ acc , counter ]) 
                                                (eval e₀ ctx []) (eval en ctx []) 

evalClosed : Exp zero m → Vec ℕ m → ℕ
evalClosed e = eval e []
\end{code}}

\begin{code}[hide]

raiseExP : ∀ {m n} (o) → Exp m n → Exp (m + o) n
raiseExP o (Var x) =  Var (inject+ o x)
raiseExP o (Lam exp) = Lam (raiseExP o exp)
raiseExP _ CZero = CZero
raiseExP _ Suc = Suc
raiseExP o (App f x) = App (raiseExP o f) (raiseExP o x)
raiseExP _ (Nat x) = Nat x
raiseExP o (PRecT h acc counter) = PRecT (raiseExP o h) (raiseExP o acc) (raiseExP o counter)


raseExp0=id : ∀ {m n}  (exp : Exp m n) → raiseExP 0 exp ≡ exp 
raseExp0=id (Var x) = cong Var (inject+0 x)
raseExp0=id (Lam exp) = cong Lam (raseExp0=id exp)
raseExp0=id CZero = refl
raseExp0=id Suc = refl
raseExp0=id (App f x) rewrite raseExp0=id f |  raseExp0=id x = refl
raseExp0=id (Nat _) = refl
raseExp0=id ((PRecT h acc counter)) rewrite raseExp0=id h | raseExp0=id acc | raseExp0=id counter = refl

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
ext2  = λ x → extensionality (λ y → extensionality (λ z → x y z))

raiseExPSound : ∀ {m n o} (exp : Exp m n) (ctx : Vec ℕ m)(ctx2 : Vec ℕ o)(args : Vec ℕ n) → eval exp ctx args ≡ eval (raiseExP o exp) (ctx ++ ctx2) args
raiseExPSound (Var x) (ctx) ctx2 _ = sym (lookup-++ˡ ctx ctx2 x)
raiseExPSound (Lam exp) ctx ctx2 (a ∷ args) rewrite raiseExPSound exp (a ∷ ctx) ctx2 args = refl
raiseExPSound CZero _ _ _ = refl
raiseExPSound Suc _ _ [ x ] = refl
raiseExPSound {m}{n} {o} (App f x) ctx ctx2 args  rewrite raiseExPSound x ctx ctx2 []  | raiseExPSound f ctx ctx2  (eval (raiseExP o x) (ctx ++ ctx2) [] ∷ args) = refl
raiseExPSound (Nat x) _ _ [] = refl
raiseExPSound (PRecT h acc counter) ctx ctx2 []  rewrite raiseExPSound acc ctx ctx2 [] |  raiseExPSound counter ctx ctx2 [] | ext2 λ x y → raiseExPSound h ctx ctx2 [ x , y ]  = refl 


------------------------------------------------------------------------------
-- helper
------------------------------------------------------------------------------

\end{code}
\newcommand{\prepLambdas}{%
\begin{code}
abstr : ∀ {o} n m →  Exp (m + n) o → Exp n (o + m)
abstr n zero    e = e
abstr n (suc m) e = Lam (abstr (suc n) m e)

abstrEval : (ctx : Vec ℕ n) (args : Vec ℕ m) (exp : Exp (m + n) 0) → 
        eval (abstr n m exp) ctx args ≡ eval exp (args ++r ctx) []
abstrEval _ [] _ = refl
abstrEval ctx (x ∷ args) exp = abstrEval (x ∷ ctx) args  exp

abstrEvalClose : (args : Vec ℕ m) (exp : Exp m zero) → 
        evalClosed (abstr 0 m exp) args ≡ eval exp (args ᴿ) []
abstrEvalClose = abstrEval []
\end{code}}
\begin{code}[hide]


------------------------------------------------------------------------------
-- constant zero-function
------------------------------------------------------------------------------

mkConstZero :   (m : ℕ) → Exp zero m 
mkConstZero m = abstr zero m CZero


evalMkConstZero : ∀  {n : ℕ } (v : Vec ℕ n ) → evalClosed (mkConstZero n) v  ≡ 0
evalMkConstZero v = abstrEvalClose v CZero 

------------------------------------------------------------------------------
-- projection
------------------------------------------------------------------------------

\end{code}

\newcommand{\mkProj}{%
\begin{code}
mkProj : Fin m → Exp zero m
mkProj {m} i = abstr zero m (Var (opposite i))

evalMkProj : ∀ {n} (i : Fin (suc n)) (args : Vec ℕ (suc n))  → 
        evalClosed (mkProj i) args ≡ lookup args i
evalMkProj i vs = begin
      eval (mkProj i) [] vs 
    ≡⟨ abstrEvalClose vs (Var (opposite i)) ⟩ 
      lookup (vs ᴿ) (opposite i) 
    ≡⟨ lookupOpRev i vs ⟩ 
      lookup vs i
    ∎ 
\end{code}}
\begin{code}[hide]
-- -- ------------------------------------------------------------------------------
-- -- -- composition
-- -- ------------------------------------------------------------------------------


mkFinvec'' : ∀ (n : ℕ ) (m : ℕ ) → Vec (Fin (n + m)) n
mkFinvec'' zero _ = []
mkFinvec'' (suc n) m = inject+ m  (fromℕ n ) ∷ (mkFinvec'' n (suc m))

mkFinvec' : ∀ (n : ℕ ) (m : ℕ ) (o : ℕ) → Vec (Fin (o + n + m)) n
mkFinvec' n m o = map (raise o) (mkFinvec'' n m)

mkFinvec : ∀ (n : ℕ ) (m : ℕ ) → Vec (Fin (n + m)) n
mkFinvec n m = mkFinvec' n m zero

apply* : ∀ {n m o : ℕ} → Exp m (n + o) → Vec (Exp m zero) o  → Exp m n
apply* exp [] = exp
apply* exp (x ∷ xs) = apply* (App exp x) xs


evalApply*=eval-map-apply :  ∀ {n m : ℕ} (exp : Exp n m) (args : Vec (Exp n zero) m) (ctx : Vec ℕ n) → eval (apply* exp args) ctx  [] ≡ eval exp  ctx (map (λ arg → eval arg ctx []) args)
evalApply*=eval-map-apply _ [] _ = refl
evalApply*=eval-map-apply {n} {suc m } exp (arg ∷ args) ctx rewrite evalApply*=eval-map-apply {n} {m} (App exp arg) args ctx = refl


maplookupEq : ∀  {o n m  : ℕ}  (zs : Vec ℕ o) (xs : Vec ℕ n) (ys : Vec ℕ m) → (map (λ x → lookup (zs ++ xs ++r ys) x) (mkFinvec' n m o)) ≡ xs
maplookupEq _ [] _  = refl
maplookupEq {o} {suc n} {m}  zs (x ∷ xs) ys   rewrite lookup-++ʳ zs (xs ++r (x ∷ ys))  (inject+ m (fromℕ n)) | lkupfromN {v = x} xs ys  = cong (λ vec → x ∷ vec) (maplookupEq  zs xs (x ∷ ys) )


mapEvalVarsEq : ∀ {o n m : ℕ} (zs : Vec ℕ o) (xs : Vec ℕ n) (ys : Vec ℕ m) →  (map (λ arg → eval arg (zs ++ xs ++r ys) []) (map Var (mkFinvec' n m o))) ≡ xs 
mapEvalVarsEq  {o} {n} {m}  zs xs ys  = begin
                                map (λ arg → eval arg (zs ++ xs ++r ys) []) (map Var (mkFinvec' n m o)) 
                                        ≡⟨ ∘-map (λ arg → eval arg (zs ++ xs ++r ys) []) Var (mkFinvec' n m o) ⟩ 
                                map ((λ arg → eval arg (zs ++ xs ++r ys) []) ∘ Var) (mkFinvec' n m o) 
                                        ≡⟨⟩ 
                                map (λ f → lookup (zs ++ xs ++r ys) f) (mkFinvec' n m o) 
                                        ≡⟨ maplookupEq zs xs ys ⟩ 
                                xs ∎



applyToVars' : ∀ {n m o} → Exp (n + m + o) m → Exp (n + m + o) zero
applyToVars' {n}{m} {o} exp  = ((flip apply* ) (map Var (mkFinvec' m o n)))  exp

applyToVars : ∀ {m o} → Exp (m + o) m → Exp (m + o) zero
applyToVars {m} {o} exp  = applyToVars' {zero} {m} {o} exp



evalApplyToVars' :  ∀ {n m o : ℕ} (exp : Exp ( n + m + o) m ) (zs : Vec ℕ (o))(xs : Vec ℕ n) (ys  : Vec ℕ m) → eval (applyToVars' {n} {m} {o} (exp)) ( xs ++ ys ++r zs) [] ≡ eval exp ( xs ++ ys ++r zs) ys
evalApplyToVars'  {n} {m} {o} exp zs xs ys  = begin
        (eval (applyToVars' exp) (xs ++ ys ++r zs) [] ) 
                ≡⟨ evalApply*=eval-map-apply (exp)  (map Var (mkFinvec' m o n)) (xs ++ ys ++r zs )⟩ 
        eval exp (xs ++ ys ++r zs)(map (λ arg → eval arg (xs ++ ys ++r zs) [])(map Var (mkFinvec' m o n)))
                ≡⟨ cong3 {x = exp} {u = (xs ++ ys ++r zs)} eval  refl refl (mapEvalVarsEq xs ys zs) ⟩ 
        (eval exp (xs ++ (ys ++r zs)) ys) ∎ 

evalApplyToVars'' :  ∀ {n m : ℕ} (exp : Exp zero n) (xs : Vec ℕ n) (ys  : Vec ℕ m) → eval (applyToVars {n} {m} (raiseExP (n + m) exp)) (xs ++r ys) [] ≡ eval exp [] xs
evalApplyToVars''  {n} {m} exp xs ys  = begin
        eval (applyToVars (raiseExP (n + m) exp)) (xs ++r ys) [] 
                        ≡⟨ evalApplyToVars' (raiseExP (n + m) exp)  ys [] xs  ⟩ 
        (eval (raiseExP (n + m) exp) ([] ++ (xs ++r ys)) xs) 
                        ≡⟨ sym (raiseExPSound exp [] ([] ++ (xs ++r ys)) xs) ⟩ (eval exp [] xs) ∎



evalApplyToVars :  ∀ {n : ℕ} (exp : Exp zero n) (vs : Vec ℕ n) → eval (applyToVars (raiseExP n exp)) (fastReverse vs) [] ≡ eval exp [] vs
evalApplyToVars  {n} exp vs  = evalApplyToVars'' exp vs []


generalComp : ∀ {n : ℕ} {m : ℕ}  → (Exp zero n) → (Vec (Exp zero m) n) → Exp zero m
generalComp {_} {m} f gs = abstr zero m (apply* (raiseExP m f) (map (applyToVars {m} {zero}) (map (raiseExP m)  gs)))

-- is thera a lemma for this? f ≡ g → map f ≡ map g
myMapCong : ∀ {A : Set} {B : Set} {n : ℕ} (f g : A → B)(vs : Vec A n) → (∀ (x : A) → f x ≡ g x) → map f vs ≡ map g vs
myMapCong f g [] eq = refl
myMapCong f g (x ∷ vs) eq rewrite eq x = cong (λ v → (g x) ∷ v) (myMapCong f g vs eq) 


evalApplyToVarsMap : ∀ {n m : ℕ} (vs : Vec ℕ n) (gs : Vec (Exp zero n) m) → map (λ exp → eval ((applyToVars {n} {zero}) (raiseExP n exp)) (fastReverse vs) []) gs ≡ map (λ exp → eval exp [] vs) gs
evalApplyToVarsMap vs [] = refl
evalApplyToVarsMap vs (g ∷ gs) rewrite evalApplyToVars g vs | evalApplyToVarsMap vs gs  = refl
evalApplyToVarsMap {n} vs gs = myMapCong ((λ exp → eval ((applyToVars {n} {zero}) (raiseExP n exp)) (fastReverse vs) [])) ((λ exp → eval exp [] vs)) gs λ x → evalApplyToVars x vs


evalGeneralCompHelper : ∀ {n m : ℕ} (args : Vec ℕ m) (gs : Vec (Exp zero m) n) → (map (λ arg → eval arg (fastReverse args) [])(map (applyToVars {m} {zero}) (map (raiseExP m) gs))) ≡
                                                                                 (map (λ exp → evalClosed exp args) gs) 
evalGeneralCompHelper {n} {m} args gs = 
                        begin (map (λ arg → eval arg (fastReverse args) [])(map (applyToVars {m} {zero}) (map (raiseExP m) gs))) 
                                ≡⟨ (∘-map (λ arg → eval arg (fastReverse args) []) (applyToVars {m} {zero}) (map (raiseExP m) gs)) ⟩ 
                        (map((λ arg → eval arg (fastReverse args) []) ∘ (applyToVars {m} {zero}))(map (raiseExP m) gs) 
                                ≡⟨  (∘-map (λ x → eval (applyToVars {m} {zero} x) (fastReverse args) []) (raiseExP m) gs) ⟩ 
                        map((λ x → eval (applyToVars x) (fastReverse args) []) ∘ raiseExP m)gs 
                                ≡⟨ evalApplyToVarsMap args gs ⟩ 
                        ((map (λ exp → evalClosed exp args) gs) ∎))
\end{code}

\newcommand{\evalGeneralComp}{%
\begin{code}
evalGeneralComp : ∀ {n m : ℕ} (f : Exp zero n) (gs : Vec (Exp zero m) n) (args : Vec  ℕ m)  → 
        evalClosed (generalComp f gs) args ≡ evalClosed f (map (λ g → evalClosed g args) gs)
\end{code}}

\begin{code}[hide]
evalGeneralComp {n} {m} f gs args = begin (evalClosed (generalComp f gs) args)
                                                ≡⟨⟩ evalClosed (abstr zero m (apply* (raiseExP m f) (map (applyToVars {m} {zero}) (map (raiseExP m)  gs)))) args 
                                                        ≡⟨ abstrEvalClose {m} args ((apply* (raiseExP m f) (map (applyToVars {m} {zero}) (map (raiseExP m)  gs)))) ⟩ 
                                                eval (apply* (raiseExP m f) (map (applyToVars {m} {zero})(map (raiseExP {zero} {m} m ) gs))) (fastReverse args) [] 
                                                        ≡⟨ evalApply*=eval-map-apply (raiseExP m f)  (map (applyToVars {m} {zero})  (map (raiseExP {zero} {m} m) gs)) (fastReverse args) ⟩ 
                                                eval (raiseExP m f) (fastReverse args)(map (λ arg → eval arg (fastReverse args) [])(map (applyToVars {m} {zero}) (map (raiseExP m) gs))) 
                                                        ≡⟨ cong3 {x = (raiseExP m f)} {u = fastReverse args} eval refl refl (evalGeneralCompHelper args gs) ⟩
                                                eval (raiseExP m f) (fastReverse args) (map (λ exp → evalClosed exp args) gs) 
                                                        ≡⟨ sym ( raiseExPSound f []  (fastReverse args) (map (λ exp → evalClosed exp args) gs)) ⟩ 
                                                eval f [] (map (λ exp → evalClosed exp args) gs) ∎ 


-- -- ------------------------------------------------------------------------------
-- -- -- primitive recursion
-- -- ------------------------------------------------------------------------------

paraT : ∀ {n} → Exp zero n → Exp zero (suc (suc n)) →  Exp zero ( (suc n))
paraT {n} g h = abstr 0 (suc n)  (PRecT 
                (Lam (Lam (applyToVars' {2} {n} {1} (App (App (raiseExP  (n + 3) h) (Var (suc zero))) (Var zero))))) 
                ((applyToVars {n} {1} (raiseExP (suc n) g)) )
                (Var (fromℕ n))) 



evalParaTHelper1 : ∀  {n x} (args : Vec ℕ n ) → (lookup (fastReverse (x ∷ args)) (fromℕ n)) ≡ x
evalParaTHelper1 {n} {x} args = lookupOpRev zero (x ∷ args)


evalParaTHelper2 :  ∀  {n x  : ℕ} (args : Vec ℕ n ) (g : Exp zero n) → (eval (applyToVars  { n} {1} (raiseExP (suc n) g)) (fastReverse (x ∷ args)) []) ≡ evalClosed g args
evalParaTHelper2  {n} {x} args g = evalApplyToVars'' g args [ x ] 



evalParaTHelper3 : ∀  {n} (x : ℕ) (counter : ℕ) (acc : ℕ) (h : Exp zero (suc (suc n))) (args : Vec ℕ n) → eval (applyToVars' {2} {n} {1} (App (App (raiseExP (suc (suc (suc n))) h) (Var (suc zero)))(Var zero))) (counter ∷ acc ∷ fastReverse (x ∷ args)) [] ≡ evalClosed h (acc ∷ counter ∷ args)
evalParaTHelper3 {n} x counter acc h args =     begin (eval (applyToVars' {2} {n} {1} (App (App (raiseExP (suc (suc (suc n))) h) (Var (suc zero)))(Var zero)))  (counter ∷ acc ∷ fastReverse (x ∷ args)) [] )
                                                        ≡⟨ evalApplyToVars' (App (App (raiseExP (suc (suc (suc n))) h) (Var (suc zero))) (Var zero)) [ x ] [ counter , acc ] args ⟩ 
                                                eval (raiseExP (suc (suc (suc n))) h) (counter ∷ acc ∷ (args ++r [ x ])) (acc ∷ counter ∷ args) 
                                                        ≡⟨ sym (raiseExPSound h [] (counter ∷ acc ∷ (args ++r [ x ]))  (acc ∷ counter ∷ args))  ⟩ (evalClosed h (acc ∷ counter ∷ args)) ∎ 

evalParaTHelper4 : ∀  {n x : ℕ} (h : Exp zero (suc (suc n))) (args : Vec ℕ n) → (λ acc counter →
         eval
         (applyToVars' {2} {n} {1}
          (App (App (raiseExP (suc (suc (suc n))) h) (Var (suc zero)))
           (Var zero)))
         (counter ∷ acc ∷ fastReverse (x ∷ args)) []) ≡ 
         (λ acc counter  → evalClosed h (acc ∷ (counter ∷ args)))
evalParaTHelper4 {n} {x} h args = ext2 (λ acc counter → evalParaTHelper3 x counter acc h args)


evalParaTHelper5 : ∀  {n x : ℕ} (g : Exp zero ( ( n))) (h : Exp zero (suc (suc n))) (args : Vec ℕ n)
        → para
      (λ acc counter →
         eval
         (applyToVars' {2} {n} {1}
          (App (App (raiseExP (suc (suc (suc n))) h) (Var (suc zero)))
           (Var zero)))
         (counter ∷ acc ∷ fastReverse (x ∷ args)) [])
      (eval (applyToVars  { n} {1}  (raiseExP (suc n) g)) (fastReverse (x ∷ args))
       [])
      (lookup (fastReverse (x ∷ args)) (fromℕ n))
      ≡
      para (λ acc counter → evalClosed h (acc ∷ counter ∷ args))
      (evalClosed g args) x
evalParaTHelper5 {n} {x} g h args rewrite evalParaTHelper1 {n} {x} args | evalParaTHelper2  {n} {x} args g | evalParaTHelper4 {n} {x} h args = refl


evalParaT : ∀ {n x : ℕ} (g : Exp zero n) (h : Exp zero (suc (suc n))) (args : Vec ℕ n ) → evalClosed (paraT g h) (x ∷ args) ≡ para (λ acc counter  → evalClosed h (acc ∷ (counter ∷ args))) (evalClosed g args) x  
evalParaT {n} {x} g h args = begin (evalClosed (paraT g h) (x ∷ args)) 
                        ≡⟨⟩ 
                ((evalClosed (abstr 0 (suc n)  (PRecT 
                (Lam (Lam (applyToVars' {2} {n} {1} (App (App (raiseExP  (n + 3) h) (Var (suc zero))) (Var zero))))) 
                ( (applyToVars {n} {1} (raiseExP (suc n) g)) )
                (Var (fromℕ n))) ) (x ∷ args)) 
                        
                        ≡⟨ abstrEvalClose (x ∷ args) (PRecT 
                        (Lam (Lam (applyToVars' {2} {n} {1} (App (App (raiseExP  (n + 3) h) (Var (suc zero))) (Var zero))))) 
                        ( (applyToVars { n} {1} (raiseExP (suc n) g)) )
                        (Var (fromℕ n))) ⟩ 
        
                para(λ acc counter → eval (applyToVars' (App (App (raiseExP (suc (suc (suc n))) h) (Var (suc zero)))(Var zero)))(counter ∷ acc ∷ fastReverse (x ∷ args)) [])(eval (applyToVars (raiseExP (suc n) g)) (fastReverse (x ∷ args))[]) (lookup (fastReverse (x ∷ args)) (fromℕ n)) 
                        
                        ≡⟨ evalParaTHelper5 {n}  {x} g h args ⟩ 
                
                (para (λ acc counter → evalClosed h (acc ∷ counter ∷ args)) (evalClosed g args) x) ∎)

\end{code}
