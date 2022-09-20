-- {-# OPTIONS --rewriting --prop -v rewriting:50 #-}
{-# OPTIONS --rewriting  #-}
{-# OPTIONS --allow-unsolved-metas #-}
module System-T0-PR-Embedding where



open import Data.Fin using (Fin; suc; zero; fromℕ; opposite; raise; inject+; inject₁; toℕ)
open import Data.Nat using (ℕ; suc; zero; _∸_; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; +-comm; +-assoc)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head; init; reverse; last; foldl) -- ; _ʳ++_) 
open import Data.Vec.Properties using (lookup-++ˡ; map-cong; lookup-++ʳ)
open import Function.Base using (const; _∘′_; id; _∘_; flip)
open import Data.Fin.Properties using (toℕ-fromℕ; fromℕ-toℕ) -- (++-assoc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂; _≗_; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Equality.Rewrite
open import NatProperties using (assoc-comm-suc)
open import FinProperties using (inject+0; inject+1; inject+Add; inject+Eq; raiseSuc)
open import VecProperties

open import System-T0 using (Exp; maplookupEq; mkFinvec; mkConstZero; mkProj; raiseExp0Eq; raiseExP; evalSTClosed; evalMkConstZero; evalMkProj; generalComp; evalGeneralComp; paraT; evalParaT; paraNat; para; paraNat'; cong3; extensionality; paraNatEq; evalST)
open System-T0.Exp

open import PR-Nat
open import Utils
open import HVec

{-# REWRITE raiseSuc  #-}



natToPR : ℕ → (m : ℕ) → PR m
natToPR zero m = Z
natToPR (suc n) m = C σ ( [ natToPR n m ])


toNRaise : ∀  (n : ℕ)  (m : ℕ) → Vec (Fin (m + n)) n
toNRaise zero m    = []
toNRaise (suc n) m = (raise m (zero {n}) ) ∷ toNRaise n (suc m)

toNInject : ∀ (n : ℕ ) (m : ℕ ) → Vec (Fin (n + m)) n
toNInject zero m = []
toNInject  (suc n) m = (subst Fin (+-comm (m) (suc n))  (inject+ n (fromℕ m))) ∷ (toNInject n (suc m))
-- lookup-++ʳ : ∀ {m n} (xs : Vec A m) (ys : Vec A n) i →
--              lookup (xs ++ ys) (Fin.raise m i) ≡ lookup ys i
-- lookup-++ʳ []       ys       zero    = refl
-- lookup-++ʳ []       (y ∷ xs) (suc i) = lookup-++ʳ [] xs i
-- lookup-++ʳ (x ∷ xs) ys       i       = lookup-++ʳ xs ys i

lookupRaise++r : ∀ {n m}  (f : Fin n) (ys : Vec ℕ m) (xs : Vec ℕ n) → lookup (ys ++r xs) (raise m f) ≡ lookup xs f 
lookupRaise++r f [] xs = refl
lookupRaise++r f (y ∷ ys) (x ∷ xs) = lookupRaise++r (suc f) ys (y ∷ (x ∷ xs))







convApp : ∀ {n m}  (f : Exp n (suc m)) (x : Exp n zero) → PR (n + m)


sTtoPR : ∀ {n m} → Exp n m → PR (n + m)
sTtoPR (Var x) = π (opposite x)
sTtoPR (Lam exp) = sTtoPR exp
sTtoPR CZero = Z
sTtoPR {n}{m} Suc = C σ [ π (fromℕ n) ]
sTtoPR {n}{m} (App f x) = convApp f x -- C (sTtoPR f) ((map π (mkFinvec n m)) ++ (C (sTtoPR x) (map π (mkFinvec n m))) ∷ map π (toNRaise m n))  
sTtoPR {n} {zero} (Nat x) = natToPR x  n
sTtoPR (PRecT h acc counter) = {!   !}

convApp {n} {m} f x = C (sTtoPR f) ((map π (toNInject n m)) ++ (C (sTtoPR x) (map π (mkFinvec n m))) ∷ map π (toNRaise m n))  


natToPRSound : ∀  {n : ℕ} (m : ℕ) (args : Vec ℕ n) → eval  (natToPR m n) args ≡ m
natToPRSound zero args = refl
natToPRSound (suc m) args = cong suc (natToPRSound m args)

{-# REWRITE inject+0  #-}




evalProjVec : ∀ {n m : ℕ} (fins : Vec (Fin n) m) (args : Vec ℕ n) → (eval* (map π fins) (args)) ≡ map (λ f → lookup args f) fins
evalProjVec {n} {.zero} [] args = refl
evalProjVec {n} {.(suc _)} (f ∷ fins) args rewrite evalProjVec fins args = refl 

evalProjVec' :  ∀ {n m : ℕ} (args : Vec ℕ m) (ctx : Vec ℕ n) → (eval* (map π (mkFinvec n m)) (ctx ++r args)) ≡ ctx
evalProjVec' {n} {m} args ctx = 
        (eval* (map π (mkFinvec n m)) (ctx ++r args)) 
    ≡⟨ evalProjVec (mkFinvec n m) (ctx ++r args) ⟩ 
        map (lookup (ctx ++r args)) (mkFinvec n m) 
    ≡⟨ maplookupEq [] ctx args ⟩ 
        ctx ∎ 


-- eval*≡map-eval

mapToNEq : ∀ {n m}  (ys : Vec ℕ m) (xs : Vec ℕ n) → map (λ f → lookup (ys ++r xs) f) (toNRaise n m)  ≡ xs 
mapToNEq ys [] = refl
mapToNEq ys (x ∷ xs) rewrite mapToNEq (x ∷ ys) xs  | lookupRaise++r zero ys  (x ∷ xs) = refl

mapToNEq' : ∀ {n m} (ys : Vec ℕ m) (xs : Vec ℕ n) → eval* ( map π (toNRaise n m)) (ys ++r xs) ≡ xs
mapToNEq' {n} {m} ys xs = 
    eval* (map π (toNRaise n m)) (ys ++r xs) 
        ≡⟨ evalProjVec (toNRaise n m) (ys ++r xs) ⟩ 
    (map (lookup (ys ++r xs)) (toNRaise n m) 
        ≡⟨ mapToNEq ys xs ⟩ xs ∎)

eqSTPRn : ∀  {n m : ℕ} ( exp : Exp n m) (ctx : Vec ℕ n ) (args : Vec ℕ m ) → eval (sTtoPR exp) (ctx ++r args) ≡ evalST exp ctx args
eqSTPRn (Var x) ctx [] = lookupOpRev x ctx
eqSTPRn (Lam exp) ctx (x ∷ args) = eqSTPRn exp (x ∷ ctx)(args)
eqSTPRn CZero ctx args = refl
eqSTPRn Suc ctx [ x ] = cong suc ( lkupfromN' ctx []  )
eqSTPRn (App f x) ctx args   = {!   !}
eqSTPRn {n} {zero} (Nat x) ctx [] = natToPRSound x (fastReverse ctx)
eqSTPRn (PRecT h acc counter) ctx [] = {!   !}


-- convAppSoundHelper1 :  ∀  {n m : ℕ} (f : Exp n (suc m)) (x : Exp n zero) → (eval*(map π (mkFinvec n m) ++ C (sTtoPR x) (map π (mkFinvec n m)) ∷ map π (toNRaise m n))(ctx ++r args)) ≡ 


-- rewrite evalProjVec' args ctx