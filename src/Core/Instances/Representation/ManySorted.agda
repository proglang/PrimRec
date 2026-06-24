{-# OPTIONS --safe #-}

module Core.Instances.Representation.ManySorted where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_; lookup)

open import Core.Instances.Common
open import Core.Instances.ManySorted
open import Core.Instances.Concrete.Evaluator using (Sem; eval)
open import Core.Instances.Concrete.Supported using (supported-con)
import Core.Instances.Concrete.ManySorted as Correct
import Core.Instances.Representation.Trees as TreeRepresentation
import Core.Instances.Source.ManySorted as Source

encode : ∀ {S s} {Sig : Source.Signature S} →
  Source.Term Sig s → Sem (Target Sig)
encode {Sig = Sig} (Source.con a children) =
  eval (supported-con (Source.ranks Sig) a)
    (TreeRepresentation.tabulateSem (lookup (Source.ranks Sig) a)
      (λ i → encode (children i)))

encodeEnv : ∀ {S n} {Sig : Source.Signature S} {ss : Vec S n} →
  Source.Env Sig ss → Sem (vec (Target Sig) n)
encodeEnv Source.[] = tt
encodeEnv (term Source.∷ terms) = encode term , encodeEnv terms

tabulate-related : ∀ {S n} {Sig : Source.Signature S}
  (ss : Vec S n)
  (values : Fin n → Sem (Target Sig))
  (terms : (i : Fin n) → Source.Term Sig (lookup ss i)) →
  ((i : Fin n) → Correct.Related (values i) (terms i)) →
  Correct.RelatedEnv ss
    (TreeRepresentation.tabulateSem n values)
    (Source.tabulateEnv terms)
tabulate-related [] values terms pointwise = Correct.related-[]
tabulate-related (s ∷ ss) values terms pointwise =
  Correct.related-∷ (pointwise zero)
    (tabulate-related ss (λ i → values (suc i))
      (λ i → terms (suc i)) (λ i → pointwise (suc i)))

represented : ∀ {S s} {Sig : Source.Signature S}
  (term : Source.Term Sig s) → Correct.Related (encode term) term
represented {Sig = Sig} (Source.con a children) =
  Correct.related-con
    (tabulate-related (Source.inputs Sig a)
      (λ i → encode (children i)) children
      (λ i → represented (children i)))

representedEnv : ∀ {S n} {Sig : Source.Signature S} {ss : Vec S n}
  (env : Source.Env Sig ss) → Correct.RelatedEnv ss (encodeEnv env) env
representedEnv Source.[] = Correct.related-[]
representedEnv (term Source.∷ terms) =
  Correct.related-∷ (represented term) (representedEnv terms)

compiler-correct-on-representations : ∀ {S n s}
  {Sig : Source.Signature S} {ss : Vec S n}
  (p : Source.PR Sig (ss , s)) (env : Source.Env Sig ss) →
  Correct.Related
    (eval (Correct.supported p) (encodeEnv env))
    (Source.eval p env)
compiler-correct-on-representations p env =
  Correct.correct p (representedEnv env)
