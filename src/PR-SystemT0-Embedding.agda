-- {-# OPTIONS --rewriting --prop -v rewriting:50 #-}
{-# OPTIONS --rewriting  #-}
{-# OPTIONS --allow-unsolved-metas #-}
module PR-SystemT0-Embedding where



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

open import System-T0 using (Exp; mkConstZero; mkProj; raiseExp0Eq; raiseExP; evalSTClosed; evalMkConstZero; evalMkProj; generalComp; evalGeneralComp; paraT; evalParaT; paraNat; para; paraNat'; cong3; extensionality; paraNatEq)
open System-T0.Exp

open import PR-Nat
open import Utils
open import HVec


-- ------------------------------------------------------------------------------
-- -- conversion
-- ------------------------------------------------------------------------------


convComp : ∀  {n m : ℕ }→ PR n → Vec (PR m) n → Exp zero m

convPR : ∀ {n} → PR n → PR (suc (suc n)) → Exp zero (suc n)



prToST' : ∀ {m : ℕ} → PR m → Exp zero m 
prToST'  {m} Z = mkConstZero m
prToST'  σ = Suc
prToST' (π i) = mkProj ( i)
prToST' (C f gs) = convComp f gs 
prToST'  (P g h) = convPR g h

prToST : (n : ℕ)  → PR m → Exp n m 
prToST n pr = raiseExP n (prToST' pr)


convCompSound : ∀ {n m} (f : PR n)  (gs : Vec  (PR m) n ) (vs : Vec ℕ m) → evalSTClosed (convComp f gs) vs  ≡  eval f (eval* gs vs)

convParaSound : ∀ {n : ℕ} (g : PR n) (h : PR (suc (suc n))) (args : Vec ℕ (suc n) ) → evalSTClosed (prToST' (P g h)) args ≡ eval (P g h) args


eqPrSTn : ∀  {n : ℕ} ( pr : PR n) (v : Vec ℕ n ) → eval pr v ≡ evalSTClosed (prToST'   pr) v
eqPrSTn {n} Z v = sym (evalMkConstZero n v)
eqPrSTn  σ [ x ] = refl
eqPrSTn  {suc n} (π i) (vs) =  sym ( evalMkProj i vs)
eqPrSTn  (C f gs) vs = sym (convCompSound f gs vs)
eqPrSTn  (P g h) vs = sym (convParaSound g h vs)                


-- -- ------------------------------------------------------------------------------
-- -- -- composition
-- -- ------------------------------------------------------------------------------



prToSt* : ∀ {m : ℕ} (o : ℕ)   → Vec (PR m) n → Vec (Exp (o) m) n
prToSt* o  [] = []
prToSt* {m} o  (x ∷ vs) = (prToST (o) x) ∷ (prToSt* o  vs)


convComp {n} {m} f gs = generalComp (prToST' f) (prToSt* zero gs)


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


paraNatPR : ∀ {n : ℕ} (g : PR n) (h : PR (suc (suc n))) (vs : Vec ℕ (suc n) ) → eval (P g h) vs ≡ paraNat (eval g) (eval h) vs
paraNatPR g h (zero ∷ vs) = refl
paraNatPR g h (suc x ∷ vs) rewrite paraNatPR  g h (x ∷ vs)  = refl 



convPR g h = paraT ((prToST'  g )) (prToST'  h)


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


