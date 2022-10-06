
{-# OPTIONS --rewriting --prop -v rewriting:50 #-}
{-# OPTIONS --allow-unsolved-metas #-}


module System-T-PR-HVec-Embedding where





open import Data.Fin using (Fin; suc; zero; opposite;fromℕ)
open import Data.Nat using (ℕ; suc; zero; _∸_; _+_)
open import Data.Nat.Properties using (+-comm)

open import Data.Vec using (Vec; []; _∷_; lookup; foldr;_++_; map)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Equality.Rewrite
-- import System-T0 as T0 --using (Exp; evalST; evalSTClosed; ext2)

-- open System-T0.Exp
open import Utils
open import HVec
open import EvalPConstructor using (para)
open import VecProperties
open import FinProperties

open import System-T using (Ctx; Ty; getArgs; Exp; countArgs)
open Ty
open Exp
open import PRHVec
open import System-T0-PR-Embedding using (toN; mToM+N; zeroToM-Inject+N; helperLookupMapRaise; helperLookupMapInject; mapToNRaiseEq; mapToNInjectEq; lookupToN=id)
-- {-# REWRITE inject+0 #-}


helper : ∀ {n : ℕ} (ctx : Ctx n)  → lookup (ctx ++r getArgs (TyNat ⇒ TyNat)) (fromℕ n) ≡ TyNat
helper ctx = lkupfromN ctx []

-- lookupToN=id
 -- mapToNInjectEq mapToNRaiseEq helperLookupMapInject

-- {-# REWRITE  #-}
helper2 : ∀ {n : ℕ}(tyA tyB : Ty) (ctx : Ctx n) → (reverse ctx ++ tyA ∷ getArgs tyB) ≡ (ctx ++r getArgs (tyA ⇒ tyB))
helper2 {_}  tyA tyB ctx = sym (++r=reverse++ ctx (tyA ∷ (getArgs tyB)) )

helper3 :  ∀ {n m : ℕ}(ctx : Ctx (n)) → (fins : Vec (Fin (n )) m) → HVec (PR (ctx)) (map (λ f → lookup  (ctx) f) fins )
helper3 ctx  [] = []ᴴ
helper3 {n} {m} (ctx) (f ∷ fins) = (π f) ∷ᴴ helper3 ctx  fins


helper4 : ∀ {n : ℕ} (ctx : Ctx n) (f : Fin n) → (map (lookup (reverse ctx ++ getArgs (lookup ctx f))) (zeroToM-Inject+N (countArgs (lookup ctx f)) n)) ≡ reverse ctx
helper4 ctx f = mapToNInjectEq (reverse ctx) (getArgs (lookup ctx f))


helper5 : ∀ {n : ℕ} (ctx : Ctx n)(tyB) → map (lookup (reverse ctx ++ getArgs tyB)) (map (Data.Fin.inject+ (countArgs tyB)) (toN n)) ≡ reverse ctx
helper5 ctx tyB = mapToNInjectEq (reverse ctx) (getArgs tyB)



{-# REWRITE helper mapToNInjectEq mapToNRaiseEq   lookupToN=id   #-}


embedd-ST-PR : ∀ {n : ℕ} {ctx : Ctx n} {ty : Ty}  → Exp ctx ty → PR  (ctx ++r (getArgs ty)) TyNat -- PR (fastReverse ctx) ty --  
embedd-ST-PR {n} {ctx} {ty} (Var f)  rewrite  (++r=reverse++ (ctx) (getArgs (lookup ctx f))) | 
                            mapToNInjectEq (reverse ctx ) (getArgs (lookup ctx f)) | 
                                                                    helper4 ctx f |
                                                                    lookupOpRev f ctx = 

  let x = C (π (opposite f)) (helper3 (reverse ctx ++ getArgs (lookup ctx f)) (zeroToM-Inject+N (countArgs (lookup ctx f))   n)) 
      y = helper3 (reverse ctx ++ getArgs (lookup ctx f)) (mToM+N  (countArgs (lookup ctx f))   n)
  
  in
    C {!  !} {!   !} -- C {!   !}  {! C ((π f))    !}
-- C (π f) (helper3 (reverse ctx ++ getArgs (lookup ctx f)) {! zeroToM-Inject+N (countArgs (lookup ctx f))   n  !}) --  |  (+-comm  ((countArgs (lookup ctx f))) n) = C (π f) {!  ty !} -- C (π f) (helper3 ((reverse ctx) ++  (getArgs (lookup ctx f))) {! mToM+N (countArgs (lookup ctx f)) n  !}) -- (helper3 (mToM+N n (countArgs (lookup ctx f) )) ) -- C (π f) {!   !} 


embedd-ST-PR {n} {ctx} {tyA ⇒ tyB} (Lam exp )= embedd-ST-PR exp 
embedd-ST-PR CZero = Z
embedd-ST-PR {n} {ctx} Suc rewrite helper ctx = C σ ({! π (fromℕ n)  !} ∷ᴴ []ᴴ) --  C σ (π (fromℕ n) ∷ᴴ []ᴴ) -- 

embedd-ST-PR {n} {ctx} {tyB} (App {_}{_}{tyA'}{tyB'} f x) 
    rewrite (sym(++r=reverse++ (ctx) (getArgs tyA'))) | ((++r=reverse++ (ctx) (getArgs tyB)))
--          |
      -- mapToNInjectEq (reverse ctx) (getArgs tyB)  |
     -- helper5 ctx tyB |  (++r=reverse++ ctx (getArgs tyA'))  
     -- helperLookupMapInject   (reverse ctx)(getArgs tyB) (toN n) 
    --  |  (++r=reverse++ (ctx) (getArgs tyB))
     -- ( (++r=reverse++ (ctx) ( ((tyA' ∷ getArgs tyB) ))))
   -- ((++r=reverse++ ctx (tyA' ∷ getArgs tyB)))  

    =   C (embedd-ST-PR f) (subst (HVec (PR (reverse ctx ++ getArgs tyB'))) (sym( ++r=reverse++ (ctx) ((tyA' ∷ getArgs tyB)))) (getCtxTyB ++ᴴ ({!  x' !} ∷ᴴ projArgsTyB)))   
            where     
            getCtxTyB = (helper3 (reverse ctx ++ getArgs tyB)   ((zeroToM-Inject+N  (countArgs (tyB)) n)))
            projArgsTyB = (helper3 (reverse ctx ++ getArgs tyB)   ((mToM+N (countArgs (tyB)) n)))

            -- getCtxTyA' = (helper3 (reverse ctx ++ getArgs tyA')   ((zeroToM-Inject+N  (countArgs (tyA')) n)))
            -- projArgsTyA' = (helper3 (reverse ctx ++ getArgs tyA')   ((mToM+N (countArgs (tyA')) n)))
            getBoth = (helper3 (reverse ctx ++ getArgs tyA')   (toN   (n + (countArgs (tyA')))))
            x' = C (embedd-ST-PR x) (subst (HVec (PR (reverse ctx ++ getArgs tyA'))) (sym (++r=reverse++ (ctx) (getArgs tyA'))) getBoth) -- (subst {! getBoth !} ((++r=reverse++ (ctx) (getArgs tyA'))) getBoth) -- (subst {!   !} {! (++r=reverse++ (ctx) (getArgs tyB))   !} {!   !})

        --     getCtx' = (helper3 ((reverse ctx) ++ ( {!   !}))   ((zeroToM-Inject+N  (countArgs (tyB)) n)))
        -- -- in                    --  -- getCtx
        --    -- C (embedd-ST-PR f) {!   !} -- (_++ᴴ_ {F = PR (reverse ctx ++ getArgs tyB)} {ss₁ = reverse ctx}  xs {! ?  !})

embedd-ST-PR (Nat x) = {!   !} -- {_} {_} {ctx}{tyA ∷ getArgs ty} ? ?
embedd-ST-PR (PrecT exp exp₁ exp₂) = {!   !}
 