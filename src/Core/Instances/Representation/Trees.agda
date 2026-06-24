{-# OPTIONS --safe #-}

module Core.Instances.Representation.Trees where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_; tabulate)

open import Core.PRFO using (TY; FO)
open import Core.Instances.Common
open import Core.Instances.Trees
open import Core.Instances.Concrete.Evaluator using (Sem; eval)
open import Core.Instances.Concrete.Supported using (supported-con)
import Core.Instances.Concrete.Trees as Correct
import Core.Instances.Source.Trees as Source

tabulateSem : ∀ {T : TY FO} (n : ℕ) →
  (Fin n → Sem T) → Sem (vec T n)
tabulateSem zero values = tt
tabulateSem (suc n) values =
  values zero , tabulateSem n (λ i → values (suc i))

encode : ∀ {R} → Source.Term R → Sem (Target R)
encode {R} (Source.con a children) =
  eval (supported-con (Source.ranks R) a)
    (tabulateSem (Source.rank R a) (λ i → encode (children i)))

encode* : ∀ {R n} → Vec (Source.Term R) n → Sem (vec (Target R) n)
encode* [] = tt
encode* (term ∷ terms) = encode term , encode* terms

tabulate-related : ∀ {R} (n : ℕ)
  (values : Fin n → Sem (Target R))
  (terms : Fin n → Source.Term R) →
  ((i : Fin n) → Correct.Related (values i) (terms i)) →
  Correct.Related* n (tabulateSem n values) (tabulate terms)
tabulate-related zero values terms pointwise = Correct.related-[]
tabulate-related (suc n) values terms pointwise =
  Correct.related-∷ (pointwise zero)
    (tabulate-related n (λ i → values (suc i))
      (λ i → terms (suc i)) (λ i → pointwise (suc i)))

represented : ∀ {R} (term : Source.Term R) →
  Correct.Related (encode term) term
represented {R} (Source.con a children) =
  Correct.related-con
    (tabulate-related (Source.rank R a)
      (λ i → encode (children i)) children
      (λ i → represented (children i)))

represented* : ∀ {R n} (terms : Vec (Source.Term R) n) →
  Correct.Related* n (encode* terms) terms
represented* [] = Correct.related-[]
represented* (term ∷ terms) =
  Correct.related-∷ (represented term) (represented* terms)

compiler-correct-on-representations : ∀ {R n}
  (p : Source.PR R n) (terms : Vec (Source.Term R) n) →
  Correct.Related
    (eval (Correct.supported p) (encode* terms))
    (Source.eval p terms)
compiler-correct-on-representations p terms =
  Correct.correct p (represented* terms)
