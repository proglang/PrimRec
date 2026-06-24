{-# OPTIONS --safe #-}

module Core.Instances.Representation.Nat where

open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)

import PR-Nat as Source
import Core.Instances.Concrete.Nat as Correct
open import Core.Instances.Concrete.Evaluator using (eval)

represented : (n : ℕ) → Correct.Related (Correct.encode n) n
represented = Correct.encode-related

represented* : ∀ {n} (xs : Vec ℕ n) →
  Correct.Related* n (Correct.encode* xs) xs
represented* = Correct.encode-related*

compiler-correct-on-representations : ∀ {n}
  (p : Source.PR n) (xs : Vec ℕ n) →
  Correct.Related
    (eval (Correct.supported p) (Correct.encode* xs))
    (Source.eval p xs)
compiler-correct-on-representations = Correct.correct-encoded
