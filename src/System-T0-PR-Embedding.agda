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
mToM+N n m = map (raise m) (toN n)


zeroToM-Inject+N : ∀  (n : ℕ)  (m : ℕ) → Vec (Fin (m + n)) m
zeroToM-Inject+N n m = map (inject+ n) (toN m)


-- lookupRaise++r : ∀ {n m}  (f : Fin n) (ys : Vec ℕ m) (xs : Vec ℕ n) → lookup (ys ++r xs) (raise m f) ≡ lookup xs f 
-- lookupRaise++r f [] xs = refl
-- lookupRaise++r f (y ∷ ys) (x ∷ xs) = lookupRaise++r (suc f) ys (y ∷ (x ∷ xs))


helperLookupConsSuc : ∀ {A : Set} {n m  : ℕ} (x : A)(xs : Vec A m)(fins : Vec  (Fin m) n) → map (lookup (x ∷ xs)) (map (suc) fins) ≡ map  (lookup ( xs)) ( fins)
helperLookupConsSuc xs x [] = refl
helperLookupConsSuc xs x (f ∷ fins) rewrite helperLookupConsSuc xs x fins =  refl

helperLookupMapRaise : ∀ {A : Set} {n m  o : ℕ} (xs : Vec A n) (ys : Vec A m) (fins : Vec  (Fin (m)) o) → map (lookup ( xs ++ ys )) (map (raise n) fins) ≡ map  (lookup ( ys)) ( fins)
helperLookupMapRaise xs ys [] = refl
helperLookupMapRaise xs ys (f ∷ fins) rewrite lookup-++ʳ xs ys f = cong ((lookup ys f) ∷_) (helperLookupMapRaise xs ys fins)

helperLookupMapInject : ∀ {A : Set} {n m  o : ℕ} (xs : Vec A n) (ys : Vec A m) (fins : Vec  (Fin (n)) o) → map (lookup ( xs ++ ys )) (map (inject+ m) fins) ≡ map  (lookup ( xs)) ( fins)
helperLookupMapInject xs ys [] = refl
helperLookupMapInject xs ys (f ∷ fins) rewrite lookup-++ˡ xs ys f = cong ((lookup xs f) ∷_) (helperLookupMapInject xs ys fins)

lookupToN=id : ∀  {A : Set} {n : ℕ} (xs : Vec A n) → map (lookup xs) (toN n) ≡ xs
lookupToN=id [] = refl
lookupToN=id {A} {suc n} (x ∷ xs) rewrite helperLookupConsSuc x xs (toN n) = cong (x ∷_) (lookupToN=id xs)


mapToNRaiseEq : ∀ {n m}  (ys : Vec ℕ m) (xs : Vec ℕ n) → map (λ f → lookup (ys ++ xs) f) (mToM+N n m)  ≡ xs 
mapToNRaiseEq {n} {m} ys xs rewrite helperLookupMapRaise ys xs (toN n) = lookupToN=id xs

mapToNInjectEq : ∀ {n m}  (ys : Vec ℕ m) (xs : Vec ℕ n) → map (λ f → lookup (ys ++ xs) f) (zeroToM-Inject+N n m)  ≡   ys 
mapToNInjectEq {n} {m} ys xs rewrite helperLookupMapInject ys xs (toN m) = lookupToN=id ys

convApp : ∀ {n m}  (f : Exp n (suc m)) (x : Exp n zero) → PR (n + m)


sTtoPR : ∀ {n m} → Exp n m → PR (n + m)
sTtoPR (Var x) = π (opposite x)
sTtoPR (Lam exp) = sTtoPR exp
sTtoPR CZero = Z
sTtoPR {n}{m} Suc = C σ [ π (fromℕ n) ]
sTtoPR {n}{m} (App f x) = convApp f x -- C (sTtoPR f) ((map π (mkFinvec n m)) ++ (C (sTtoPR x) (map π (mkFinvec n m))) ∷ map π (mToM+N m n))  
sTtoPR {n} {zero} (Nat x) = natToPR x  n
sTtoPR (PRecT h acc counter) = {!   !}

convApp {n} {m} f x = C (sTtoPR f) ((map π (zeroToM-Inject+N m n)) ++ (C (sTtoPR x) (map π (zeroToM-Inject+N m n))) ∷ map π (mToM+N m n))  


natToPRSound : ∀  {n : ℕ} (m : ℕ) (args : Vec ℕ n) → eval  (natToPR m n) args ≡ m
natToPRSound zero args = refl
natToPRSound (suc m) args = cong suc (natToPRSound m args)

{-# REWRITE inject+0  #-}


evalProjVec'=map-lookup : ∀ {n m : ℕ} (fins : Vec (Fin n) m) (args : Vec ℕ n) → map (λ p → eval p args) (map π ( fins))  ≡ map (λ f → lookup args f) fins
evalProjVec'=map-lookup {n} {.zero} [] args = refl
evalProjVec'=map-lookup {n} {.(suc _)} (f ∷ fins) args rewrite evalProjVec'=map-lookup fins args = refl 


injectAppSoundHelper1 :  ∀  {n m : ℕ} (args : Vec ℕ m) (ctx : Vec ℕ n) (x : PR n) → (eval* (map π (zeroToM-Inject+N m n) ++ C (x) (map π (zeroToM-Inject+N m n)) ∷ map π (mToM+N m n)) (ctx ++r args)) ≡ (ctx ++r (eval x (fastReverse ctx) ∷ args)) -- (reverse ctx) ++ ((eval x (reverse ctx)) ∷ args)
injectAppSoundHelper1 {n} {m} args ctx x rewrite 
        eval*≡map-eval  (map π (zeroToM-Inject+N m n) ++ C x (map π (zeroToM-Inject+N m n)) ∷ map π (mToM+N m n))  (ctx ++r args) |
        sym(++-map (λ p → eval p (ctx ++r args)) (map π (zeroToM-Inject+N m n)) (C x (map π (zeroToM-Inject+N m n)) ∷ map π (mToM+N m n)))  | 
        eval*≡map-eval (map π (map (inject+ m) (toN n))) (ctx ++r args)  |
        evalProjVec'=map-lookup (map (inject+ m) (toN n)) (ctx ++r args) |
        ++r-reverse' ctx args |
        mapToNInjectEq  (reverse ctx) args |
        evalProjVec'=map-lookup ((map (raise n) (toN m))) ((reverse ctx) ++ args) |
        mapToNRaiseEq  (reverse ctx) args |
        sym (++r-reverse' ctx (eval x (reverse ctx) ∷ args) ) |
        reverse=fastReverse ctx
        = refl


convAppSound :  ∀  {n m : ℕ}  (f : Exp n (suc m)) (x : Exp n zero) (ctx : Vec ℕ n) (args : Vec ℕ m)  → eval (convApp f x) (ctx ++r args)   ≡ evalST f ctx (evalST x ctx [] ∷ args)


embeddST-PR-Sound : ∀  {n m : ℕ} ( exp : Exp n m) (ctx : Vec ℕ n ) (args : Vec ℕ m ) → eval (sTtoPR exp) (ctx ++r args) ≡ evalST exp ctx args
embeddST-PR-Sound (Var x) ctx [] = lookupOpRev x ctx
embeddST-PR-Sound (Lam exp) ctx (x ∷ args) = embeddST-PR-Sound exp (x ∷ ctx)(args)
embeddST-PR-Sound CZero ctx args = refl
embeddST-PR-Sound Suc ctx [ x ] = cong suc ( lkupfromN' ctx []  )
embeddST-PR-Sound (App f x) ctx args   = convAppSound f x ctx args
embeddST-PR-Sound {n} {zero} (Nat x) ctx [] = natToPRSound x (fastReverse ctx)
embeddST-PR-Sound (PRecT h acc counter) ctx [] = {!   !}


convAppSound f x ctx args rewrite injectAppSoundHelper1 args ctx (sTtoPR x) | embeddST-PR-Sound x ctx [] | embeddST-PR-Sound f ctx (evalST x ctx [] ∷ args) = refl

