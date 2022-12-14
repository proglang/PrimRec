
\begin{code}[hide]
{-# OPTIONS --rewriting  #-}
module PR-SystemT0-Embedding where



open import Data.Nat using (ℕ; suc; zero)
open import Data.Vec using (Vec; []; _∷_; map) 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import System-T0 using (Exp; mkConstZero; mkProj; raseExp0=id; raiseExP; evalClosed; evalMkConstZero; evalMkProj; generalComp; evalGeneralComp; paraT; evalParaT; cong3; extensionality)
open System-T0.Exp
open import EvalPConstructor using (para; paraNat'; evalP≡paraNat')


open import PR-Nat
open import Utils


-- ------------------------------------------------------------------------------
-- -- conversion
-- ------------------------------------------------------------------------------


convComp : ∀  {n m : ℕ }→ PR n → Vec (PR m) n → Exp zero m

convPR : ∀ {n} → PR n → PR (suc (suc n)) → Exp zero (suc n)

\end{code}

\newcommand{\prToStSig}{%
\begin{code}
prToST′ : PR m → Exp zero m
\end{code}}



\begin{code}[hide]
-- prToST′  {m} Z =  mkConstZero m
prToST′  {m} Z =  CZero
prToST′  σ = Suc
\end{code}

\newcommand{\prToStProj}{%
\begin{code}
prToST′ (π i) = mkProj i
\end{code}}

\begin{code}[hide]
prToST′ (C f gs) = convComp f gs 
prToST′  (P g h) = convPR g h

prToST : (n : ℕ)  → PR m → Exp n m 
prToST n pr = raiseExP n (prToST′ pr)


convCompSound : ∀ {n m} (f : PR n)  (gs : Vec  (PR m) n ) (vs : Vec ℕ m) → evalClosed (convComp f gs) vs  ≡  eval f (eval* gs vs)

convParaSound : ∀ {n : ℕ} (g : PR n) (h : PR (suc (suc n))) (args : Vec ℕ (suc n) ) → evalClosed (prToST′ (P g h)) args ≡ eval (P g h) args

\end{code}

\newcommand{\embedPRSTSoundSig}{%
\begin{code}
embeddPR-ST-Sound : (pr : PR n) (vs : Vec ℕ n) → 
        evalClosed (prToST′   pr) vs ≡ eval pr vs
\end{code}}


\begin{code}[hide]
-- embeddPR-ST-Sound {n} Z v =  evalMkConstZero n v
embeddPR-ST-Sound  Z [] = refl 
\end{code}

\newcommand{\embedPRSTSoundProj}{%
\begin{code}
embeddPR-ST-Sound {suc n} (π i) vs = evalMkProj i vs
\end{code}}

\begin{code}[hide]
embeddPR-ST-Sound  σ [ x ] = refl
embeddPR-ST-Sound  (C f gs) vs =  convCompSound f gs vs
embeddPR-ST-Sound  (P g h) vs = convParaSound g h vs            


-- -- ------------------------------------------------------------------------------
-- -- -- composition
-- -- ------------------------------------------------------------------------------



prToSt* : ∀ {m : ℕ}    → Vec (PR m) n → Vec (Exp zero m) n
prToSt*  [] = []
prToSt*  (x ∷ vs) = (prToST′  x) ∷ (prToSt*  vs)

convComp f gs = generalComp (prToST′ f) (prToSt*  gs)


eval*≡evalPrToST* : ∀ {n m}  (vs : Vec ℕ m) (gs : Vec (PR m) n) → (map (λ g → evalClosed g vs) (prToSt* gs)) ≡ (eval* gs vs)
eval*≡evalPrToST* vs [] = refl
eval*≡evalPrToST* vs (g ∷ gs) rewrite embeddPR-ST-Sound  g vs | eval*≡evalPrToST* vs gs | raseExp0=id (prToST′ g) = refl

convCompSoundHelper : ∀ {n m} (f : PR n) (vs : Vec ℕ m) (gs : Vec (PR m) n) → evalClosed (prToST′ f) (map (λ g → evalClosed g vs) (prToSt* gs))≡ eval f (eval* gs vs)
convCompSoundHelper f vs gs rewrite eval*≡evalPrToST* vs gs | embeddPR-ST-Sound f (eval* gs vs) = refl

convCompSound f gs vs = begin 
                (evalClosed (convComp f gs) vs) 
        ≡⟨⟩ 
                (((evalClosed (generalComp (prToST′ f) (prToSt* gs)) vs)) 
        ≡⟨ evalGeneralComp (prToST′ f) (prToSt* gs) vs ⟩ 
                (evalClosed (prToST′ f)  (map (λ g → evalClosed g vs) (prToSt* gs)) 
        ≡⟨ convCompSoundHelper f  vs gs ⟩ 
                (eval f (eval* gs vs)) ∎ ))


-- -- ------------------------------------------------------------------------------
-- -- -- primitive recursion
-- -- ------------------------------------------------------------------------------



convPR g h = paraT ((prToST′  g )) (prToST′  h)


convParaSound g h (x ∷ args) = begin 
                        (evalClosed (prToST′ (P g h)) (x ∷ args))
                                ≡⟨⟩ 
                        evalClosed (paraT ((prToST′  g )) (prToST′  h)) (x ∷ args) 
                                ≡⟨ evalParaT (prToST′  g ) (prToST′  h) args ⟩ 
                        para (λ acc counter → evalClosed (prToST′ h) (acc ∷ counter ∷ args)) (evalClosed (prToST′ g) args) x 
                                ≡⟨⟩ 
                        paraNat' (evalClosed (prToST′ g)) (evalClosed (prToST′ h)) ((x ∷ args)) 
                                ≡⟨ cong3 { w = x ∷ args } paraNat'  ((extensionality (λ v →  embeddPR-ST-Sound g v))) (((extensionality (λ v →  (embeddPR-ST-Sound h v))))) refl  ⟩  
                        (para (λ acc n → eval h (acc ∷ n ∷ args)) (eval g args) x) 
                                ≡⟨ sym (evalP≡paraNat' g h (x ∷ args) ) ⟩ 
                        (eval (P g h) (x ∷ args)) ∎
\end{code}
