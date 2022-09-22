-- {-# OPTIONS --rewriting --prop -v rewriting:50 #-}
{-# OPTIONS --rewriting  #-}
{-# OPTIONS --allow-unsolved-metas #-}
module System-T0-PR-Embedding where



open import Data.Fin using (Fin; suc; zero; opposite; raise; inject+; fromℕ)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map) -- ; _ʳ++_) 
open import Data.Vec.Properties using (lookup-++ˡ; map-cong; lookup-++ʳ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Equality.Rewrite

open import FinProperties using (inject+0)
open import VecProperties using (_++r_; fastReverse; ++r=reverse++; reverse; reverse=fastReverse; lookupOpRev; lkupfromN)
open import System-T0 using (Exp; ext2; maplookupEq; evalSTClosed; paraNat; para; cong3; paraNatEq; evalST)
open System-T0.Exp
open import PR-SystemT0-Embedding using (paraNatPR)
open import PR-Nat
open import Utils


-- -- ------------------------------------------------------------------------------
-- -- -- helper
-- -- ------------------------------------------------------------------------------


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



-- -- ------------------------------------------------------------------------------
-- -- -- embedding
-- -- ------------------------------------------------------------------------------

convApp : ∀ {n m}  (f : Exp n (suc m)) (x : Exp n zero) → PR (n + m)


convPR : (h : Exp n 2) (acc : Exp n 0) (counter : Exp n 0) → PR (n)


sTtoPR : ∀ {n m} → Exp n m → PR (n + m)
sTtoPR (Var x) = π (opposite x)
sTtoPR (Lam exp) = sTtoPR exp
sTtoPR CZero = Z
sTtoPR {n}{m} Suc = C σ [ π (fromℕ n) ]
sTtoPR {n}{m} (App f x) = convApp f x
sTtoPR {n} {zero} (Nat x) = natToPR x  n
sTtoPR (PRecT h acc counter) = convPR h acc counter

embeddST-PR-Sound : ∀  {n m : ℕ} ( exp : Exp n m) (ctx : Vec ℕ n ) (args : Vec ℕ m ) → eval (sTtoPR exp) (ctx ++r args) ≡ evalST exp ctx args


natToPRSound : ∀  {n : ℕ} (m : ℕ) (args : Vec ℕ n) → eval  (natToPR m n) args ≡ m
natToPRSound zero args = refl
natToPRSound (suc m) args = cong suc (natToPRSound m args)

{-# REWRITE inject+0  #-}

-- -- ------------------------------------------------------------------------------
-- -- -- App
-- -- ------------------------------------------------------------------------------


evalProjVec=map-lookup : ∀ {n m : ℕ} (fins : Vec (Fin n) m) (args : Vec ℕ n) → map (λ p → eval p args) (map π ( fins))  ≡ map (λ f → lookup args f) fins
evalProjVec=map-lookup {n} {.zero} [] args = refl
evalProjVec=map-lookup {n} {.(suc _)} (f ∷ fins) args rewrite evalProjVec=map-lookup fins args = refl 

mkApp : ∀ {n m} → PR (n + suc m) → PR n → PR (n + m)
mkApp {n} {m} f x = C (f) ((map π (zeroToM-Inject+N m n)) ++ (C ( x) (map π (zeroToM-Inject+N m n))) ∷ map π (mToM+N m n))


convApp {n} {m} f x = mkApp {n} {m} (sTtoPR f) (sTtoPR x)


evalAppHelper :  ∀  {n m : ℕ} (args : Vec ℕ m) (ctx : Vec ℕ n) (x : PR n) → (eval* (map π (zeroToM-Inject+N m n) ++ C (x) (map π (zeroToM-Inject+N m n)) ∷ map π (mToM+N m n)) (ctx ++r args)) ≡ (ctx ++r (eval x (fastReverse ctx) ∷ args)) -- (reverse ctx) ++ ((eval x (reverse ctx)) ∷ args)
evalAppHelper {n} {m} args ctx x rewrite 
        eval*≡map-eval  (map π (zeroToM-Inject+N m n) ++ C x (map π (zeroToM-Inject+N m n)) ∷ map π (mToM+N m n))  (ctx ++r args) |
        sym(++-map (λ p → eval p (ctx ++r args)) (map π (zeroToM-Inject+N m n)) (C x (map π (zeroToM-Inject+N m n)) ∷ map π (mToM+N m n)))  | 
        eval*≡map-eval (map π (map (inject+ m) (toN n))) (ctx ++r args)  |
        evalProjVec=map-lookup (map (inject+ m) (toN n)) (ctx ++r args) |
        ++r=reverse++ ctx args |
        mapToNInjectEq  (reverse ctx) args |
        evalProjVec=map-lookup ((map (raise n) (toN m))) ((reverse ctx) ++ args) |
        mapToNRaiseEq  (reverse ctx) args |
        sym (++r=reverse++ ctx (eval x (reverse ctx) ∷ args) ) |
        reverse=fastReverse ctx
        = refl

evalAppEq : ∀ {n m} (f : PR (n + suc m)) (x : PR n) (ctx : Vec ℕ n) (args : Vec ℕ m) → eval (mkApp {n} {m} f x) (ctx ++r args) ≡ eval ( f) (ctx ++r (eval ( x) (ctx ++r []) ∷ args))
evalAppEq f x ctx args  rewrite evalAppHelper args ctx x = refl


convAppSound :  ∀  {n m : ℕ}  (f : Exp n (suc m)) (x : Exp n zero) (ctx : Vec ℕ n) (args : Vec ℕ m)  → eval (convApp f x) (ctx ++r args)   ≡ evalST f ctx (evalST x ctx [] ∷ args)
convAppSound f x ctx args rewrite evalAppEq (sTtoPR f ) (sTtoPR  x) ctx args | embeddST-PR-Sound x ctx [] | embeddST-PR-Sound f ctx (evalST x ctx [] ∷ args) = refl


-- -- ------------------------------------------------------------------------------
-- -- -- PR
-- -- ------------------------------------------------------------------------------

swapArgs : ∀ (n) → Vec (PR (n + 2))(n + 2)
swapArgs n = map π ((mToM+N n 2) ++ zeroToM-Inject+N n 2)

eval*swapArgs : ∀ {n : ℕ} (x y : ℕ)(xs : Vec ℕ n) → (eval* (swapArgs n) (x ∷ y ∷ xs)) ≡ xs ++ [ x , y ]
eval*swapArgs {n} x y xs 
        rewrite eval*≡map-eval (swapArgs n) (x ∷ y ∷ xs)  | 
        sym (++-map π (mToM+N n 2) (zeroToM-Inject+N n 2)) | 
        sym (++-map (λ p → eval p (x ∷ y ∷ xs))  (map π  (mToM+N n 2))  (map π (zeroToM-Inject+N n 2))) | 
        evalProjVec=map-lookup (map (λ i → suc (suc i)) (toN n))  (x ∷ y ∷ xs) |
        helperLookupMapRaise [ x , y ]  xs ( (toN n))  = cong (λ v → v ++ [ x , y ]) (lookupToN=id xs)


mkPR : ∀  {n : ℕ} → PR (suc (suc n))  → PR n → PR n → PR n
mkPR {n} h acc counter = C  (P acc (C h (swapArgs n)) ) (counter ∷ map π (toN n))


evalmkPr : ∀  {n : ℕ}  (h : PR (suc (suc n))) (acc : PR n) (counter : PR n) (ctx : Vec ℕ n) → eval (mkPR h acc counter) (fastReverse ctx) ≡ eval (P acc (C h (swapArgs n)) ) ((eval (counter) (fastReverse ctx) ∷ (fastReverse ctx)))
evalmkPr {n} h acc counter ctx rewrite eval*≡map-eval (map π (toN n)) (fastReverse ctx)  | evalProjVec=map-lookup (toN n) (fastReverse ctx) |  lookupToN=id  (fastReverse ctx) = refl


convPR h acc counter = mkPR (sTtoPR h) (sTtoPR acc) (sTtoPR counter)


convPRSoundHelper : ∀  {n : ℕ} (x) (y) (h : Exp n 2) (ctx : Vec ℕ n) → eval (sTtoPR h) (eval* (swapArgs n) (x ∷ y ∷ fastReverse ctx)) ≡ evalST h ctx [ x , y ]
convPRSoundHelper x y h ctx rewrite eval*swapArgs x y (fastReverse ctx) | reverse=fastReverse ctx | sym(++r=reverse++ ctx [ x , y ]  ) = embeddST-PR-Sound h ctx [ x , y ]



-- convPRSoundHelper : ∀  {n : ℕ}  (h : Exp n 2) (acc : Exp n 0) (counter : Exp n 0) (ctx : Vec ℕ n) → 
--         para
--     (λ acc₁ n₁ →
--        eval (sTtoPR h) (eval* (swapArgs n) (acc₁ ∷ n₁ ∷ fastReverse ctx)))
--     (eval (sTtoPR acc) (fastReverse ctx))
--     (eval (sTtoPR counter) (fastReverse ctx))
--       ≡
--       para (λ acc' counter' → evalST h ctx [ acc' , counter' ])
--       (evalST acc ctx []) (evalST counter ctx [])
-- convPRSoundHelper h acc counter ctx  = cong3 para (ext2 (λ x y → helper x y h ctx)) (embeddST-PR-Sound acc ctx []) (embeddST-PR-Sound counter ctx []) 


convPRSound : ∀  {n : ℕ}  (h : Exp n 2) (acc : Exp n 0) (counter : Exp n 0) (ctx : Vec ℕ n) → eval (convPR h acc counter) (fastReverse ctx)  ≡ para (λ acc' counter' → evalST h ctx [ acc' , counter' ]) (evalST acc ctx []) (evalST counter ctx [])
convPRSound {n} h acc counter ctx  = 
        (eval (convPR h acc counter) (fastReverse ctx)) 
                ≡⟨ evalmkPr (sTtoPR h) (sTtoPR acc) (sTtoPR counter) ctx ⟩ 
        (eval (P (sTtoPR acc) (C (sTtoPR h) (swapArgs n))) (eval (sTtoPR counter) (fastReverse ctx) ∷ fastReverse ctx) 
                ≡⟨ paraNatPR (sTtoPR acc) (C (sTtoPR h) (swapArgs n)) (eval (sTtoPR counter) (fastReverse ctx) ∷ fastReverse ctx) ⟩ 
        paraNat (eval (sTtoPR acc)) (eval ((C (sTtoPR h) (swapArgs n))))(eval (sTtoPR counter) (fastReverse ctx) ∷ fastReverse ctx) 
                 ≡⟨ paraNatEq (eval (sTtoPR acc)) (eval ((C (sTtoPR h) (swapArgs n)))) (eval (sTtoPR counter) (fastReverse ctx) ∷ fastReverse ctx) ⟩ 
        para (λ acc₁ n₁ → eval (sTtoPR h) (eval* (swapArgs n) (acc₁ ∷ n₁ ∷ fastReverse ctx)))(eval (sTtoPR acc) (fastReverse ctx))(eval (sTtoPR counter) (fastReverse ctx))
                ≡⟨ cong3 para (ext2 (λ x y → convPRSoundHelper x y h ctx)) (embeddST-PR-Sound acc ctx []) (embeddST-PR-Sound counter ctx [])  ⟩ 
        (para (λ acc' counter' → evalST h ctx [ acc' , counter' ])(evalST acc ctx []) (evalST counter ctx [])) ∎  )




-- -- ------------------------------------------------------------------------------
-- -- -- Sound-Embedding
-- -- ------------------------------------------------------------------------------


embeddST-PR-Sound (Var x) ctx [] = lookupOpRev x ctx
embeddST-PR-Sound (Lam exp) ctx (x ∷ args) = embeddST-PR-Sound exp (x ∷ ctx)(args)
embeddST-PR-Sound CZero ctx args = refl
embeddST-PR-Sound Suc ctx [ x ] = cong suc ( lkupfromN ctx []  )
embeddST-PR-Sound (App f x) ctx args   = convAppSound f x ctx args
embeddST-PR-Sound {n} {zero} (Nat x) ctx [] = natToPRSound x (fastReverse ctx)
embeddST-PR-Sound (PRecT h acc counter) ctx [] = convPRSound h acc counter ctx -- 