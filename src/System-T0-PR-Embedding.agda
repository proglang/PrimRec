-- {-# OPTIONS --rewriting --prop -v rewriting:50 #-}
{-# OPTIONS --rewriting  #-}
{-# OPTIONS --allow-unsolved-metas #-}
module System-T0-PR-Embedding where



open import Data.Fin using (Fin; suc; zero; fromℕ; opposite; raise; inject+; inject₁; toℕ)
open import Data.Nat using (ℕ; suc; zero; _∸_; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; +-comm; +-assoc)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head; init; last; foldl) -- ; _ʳ++_) 
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

toN : (n : ℕ) → Vec (Fin n) n
toN zero = []
toN (suc n) = zero ∷ (map suc (toN n))

mToM+N : ∀  (n : ℕ)  (m : ℕ) → Vec (Fin (m + n)) n
-- mToM+N zero m    = []
-- mToM+N (suc n) m = (raise m (zero {n}) ) ∷ mToM+N n (suc m)
mToM+N n m = map (raise m) (toN n)

-- zeroToM-Inject+N' : ∀  (n : ℕ)  (m : ℕ) → Vec (Fin (m + n)) m
-- zeroToM-Inject+N' n m = map (inject+ n) (mToM+N m zero)


zeroToM-Inject+N' : ∀  (n : ℕ)  (m : ℕ) → Vec (Fin (m + n)) m
zeroToM-Inject+N' n zero = []
zeroToM-Inject+N' n (suc m) = zero ∷ (map suc (zeroToM-Inject+N' n m))

_ : zeroToM-Inject+N' 3 2 ≡ zero ∷ (suc zero ∷ [])
_ = refl


lookupRaise++r : ∀ {n m}  (f : Fin n) (ys : Vec ℕ m) (xs : Vec ℕ n) → lookup (ys ++r xs) (raise m f) ≡ lookup xs f 
lookupRaise++r f [] xs = refl
lookupRaise++r f (y ∷ ys) (x ∷ xs) = lookupRaise++r (suc f) ys (y ∷ (x ∷ xs))


helperLookupConsSuc : ∀ {A : Set} {n m  : ℕ} (x : A)(xs : Vec A m)(fins : Vec  (Fin m) n) → map (lookup (x ∷ xs)) (map (suc) fins) ≡ map  (lookup ( xs)) ( fins)
helperLookupConsSuc xs x [] = refl
helperLookupConsSuc xs x (f ∷ fins) rewrite helperLookupConsSuc xs x fins =  refl

helperLookupMapRaise : ∀ {A : Set} {n m  o : ℕ} (xs : Vec A n) (ys : Vec A m) (fins : Vec  (Fin (m)) o) → map (lookup ( xs ++ ys )) (map (raise n) fins) ≡ map  (lookup ( ys)) ( fins)
helperLookupMapRaise xs ys [] = refl
helperLookupMapRaise xs ys (f ∷ fins) rewrite lookup-++ʳ xs ys f = cong ((lookup ys f) ∷_) (helperLookupMapRaise xs ys fins)

convApp : ∀ {n m}  (f : Exp n (suc m)) (x : Exp n zero) → PR (n + m)


sTtoPR : ∀ {n m} → Exp n m → PR (n + m)
sTtoPR (Var x) = π (opposite x)
sTtoPR (Lam exp) = sTtoPR exp
sTtoPR CZero = Z
sTtoPR {n}{m} Suc = C σ [ π (fromℕ n) ]
sTtoPR {n}{m} (App f x) = convApp f x -- C (sTtoPR f) ((map π (mkFinvec n m)) ++ (C (sTtoPR x) (map π (mkFinvec n m))) ∷ map π (mToM+N m n))  
sTtoPR {n} {zero} (Nat x) = natToPR x  n
sTtoPR (PRecT h acc counter) = {!   !}

convApp {n} {m} f x = C (sTtoPR f) ((map π (zeroToM-Inject+N' m n)) ++ (C (sTtoPR x) (map π (zeroToM-Inject+N' m n))) ∷ map π (mToM+N m n))  


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

mapToNRaiseEq : ∀ {n m}  (ys : Vec ℕ m) (xs : Vec ℕ n) → map (λ f → lookup (ys ++r xs) f) (mToM+N n m)  ≡ xs 
mapToNRaiseEq ys [] = refl
mapToNRaiseEq ys (x ∷ xs)  = {!   !}

mapToNRaiseEq'' : ∀ {n m}  (ys : Vec ℕ m) (xs : Vec ℕ n) → map (λ f → lookup (ys ++ xs) f) (mToM+N n m)  ≡ xs 
mapToNRaiseEq'' ys [] = refl
mapToNRaiseEq'' ys (x ∷ xs) rewrite lookup-++ʳ ys (x ∷ xs) zero = cong (x ∷_) {!   !}
-- mapToNRaiseEq'' [] (x ∷ xs) = cong (λ v → x ∷ v) (mapToNRaiseEq'' [ x ] xs)
-- mapToNRaiseEq'' {suc n} {suc m} (y ∷ ys) (x ∷ xs) rewrite lookup-++ʳ ys (x ∷ xs) zero  = cong (x ∷_) {!   !}

-- mapToNRaiseEq' : ∀ {n m} (ys : Vec ℕ m) (xs : Vec ℕ n) → eval* ( map π (mToM+N n m)) (ys ++r xs) ≡ xs
-- mapToNRaiseEq' {n} {m} ys xs = 
--     eval* (map π (mToM+N n m)) (ys ++r xs) 
--         ≡⟨ evalProjVec (mToM+N n m) (ys ++r xs) ⟩ 
--     (map (lookup (ys ++r xs)) (mToM+N n m) 
--         ≡⟨ mapToNRaiseEq ys xs ⟩ xs ∎)




mapToNInjectEq : ∀ {n m}  (ys : Vec ℕ m) (xs : Vec ℕ n) → map (λ f → lookup (ys ++ xs) f) (zeroToM-Inject+N' n m)  ≡   ys 
mapToNInjectEq [] (xs) = refl
mapToNInjectEq {n} {suc m} (y ∷ ys) xs rewrite helperLookupConsSuc y (ys ++ xs)  (zeroToM-Inject+N' n m) = cong (λ v → y ∷ v) (mapToNInjectEq ys xs)




eqSTPRn : ∀  {n m : ℕ} ( exp : Exp n m) (ctx : Vec ℕ n ) (args : Vec ℕ m ) → eval (sTtoPR exp) (ctx ++r args) ≡ evalST exp ctx args
eqSTPRn (Var x) ctx [] = lookupOpRev x ctx
eqSTPRn (Lam exp) ctx (x ∷ args) = eqSTPRn exp (x ∷ ctx)(args)
eqSTPRn CZero ctx args = refl
eqSTPRn Suc ctx [ x ] = cong suc ( lkupfromN' ctx []  )
eqSTPRn (App f x) ctx args   = {!   !}
eqSTPRn {n} {zero} (Nat x) ctx [] = natToPRSound x (fastReverse ctx)
eqSTPRn (PRecT h acc counter) ctx [] = {!   !}


-- convAppSoundHelper1 :  ∀  {n m : ℕ} (f : Exp n (suc m)) (x : Exp n zero) → (eval*(map π (mkFinvec n m) ++ C (sTtoPR x) (map π (mkFinvec n m)) ∷ map π (mToM+N m n))(ctx ++r args)) ≡ 


-- rewrite evalProjVec' args ctx 

injectAppSoundHelper1 :  ∀  {n m : ℕ} (args : Vec ℕ m) (ctx : Vec ℕ n) (x) → (eval* (map π (zeroToM-Inject+N' m n) ++ C (x) (map π (zeroToM-Inject+N' m n)) ∷ map π (mToM+N m n)) (ctx ++r args)) ≡ (reverse ctx) ++ ((eval x (reverse ctx)) ∷ args)
injectAppSoundHelper1 {n} {m} args ctx x rewrite 
        eval*≡map-eval  (map π (zeroToM-Inject+N' m n) ++ C x (map π (zeroToM-Inject+N' m n)) ∷ map π (mToM+N m n))  (ctx ++r args) |
        sym(++-map (λ p → eval p (ctx ++r args)) (map π (zeroToM-Inject+N' m n)) (C x (map π (zeroToM-Inject+N' m n)) ∷ map π (mToM+N m n)))  
        = {!   !}