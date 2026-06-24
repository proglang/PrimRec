{-# OPTIONS --safe #-}

module Core.Instances.Representation.Words where

open import Data.List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_)

import PR-Words as Source
import Core.Finite as Finite
open import Core.Instances.Common
open import Core.Instances.Words
open import Core.Instances.Concrete.Evaluator
open import Core.Instances.Concrete.Supported using (supported-con)
import Core.Instances.Concrete.Words as Correct

encode : ∀ {k} → List (Fin k) → Sem (Word k)
encode {k} []ᴸ = eval (Correct.supported-emptyCon {k}) tt
encode (a ∷ᴸ xs) =
  eval (Correct.supported-letterCon a) (encode xs , tt)

encode* : ∀ {k n} → Vec (List (Fin k)) n → Sem (vec (Word k) n)
encode* [] = tt
encode* (x ∷ xs) = encode x , encode* xs

represented : ∀ {k} (xs : List (Fin k)) → Correct.Related (encode xs) xs
represented {k} []ᴸ = Correct.related-[] {k = k}
represented (a ∷ᴸ xs) = Correct.related-∷ (represented xs)

represented* : ∀ {k n} (xs : Vec (List (Fin k)) n) →
  Correct.Related* n (encode* xs) xs
represented* [] = Correct.related-v[]
represented* (x ∷ xs) = Correct.related-v∷ (represented x) (represented* xs)

compiler-correct-on-representations : ∀ {k n}
  (p : Source.PR (Fin k) n)
  (xs : Vec (List (Fin k)) n) →
  Correct.Related
    (eval (Correct.supported p) (encode* xs))
    (Source.eval p xs)
compiler-correct-on-representations p xs = Correct.correct p (represented* xs)

----------------------------------------------------------------------
-- Representations for an arbitrary finitely presented alphabet
----------------------------------------------------------------------

module ForFinite {A : Set} (finiteA : Finite.Finite A) where
  module W = Core.Instances.Words.For finiteA
  module CorrectF = Correct.ForFinite finiteA

  k : ℕ
  k = Finite.size finiteA

  encodeFinite : List A → Sem (Word k)
  encodeFinite []ᴸ = eval (Correct.supported-emptyCon {k}) tt
  encodeFinite (a ∷ᴸ xs) =
    eval (Correct.supported-letterCon (Finite.encode finiteA a))
      (encodeFinite xs , tt)

  encodeFinite* : ∀ {n} → Vec (List A) n → Sem (vec (Word k) n)
  encodeFinite* [] = tt
  encodeFinite* (x ∷ xs) = encodeFinite x , encodeFinite* xs

  representedFinite : (xs : List A) →
    CorrectF.RelatedFinite (encodeFinite xs) xs
  representedFinite []ᴸ = CorrectF.related-[]
  representedFinite (a ∷ᴸ xs) =
    CorrectF.related-∷ (representedFinite xs)

  representedFinite* : ∀ {n} (xs : Vec (List A) n) →
    CorrectF.RelatedFinite* n (encodeFinite* xs) xs
  representedFinite* [] = CorrectF.related-v[]
  representedFinite* (x ∷ xs) =
    CorrectF.related-v∷ (representedFinite x) (representedFinite* xs)

  compiler-correct-finite : ∀ {n} (p : Source.PR A n)
    (xs : Vec (List A) n) →
    CorrectF.RelatedFinite
      (eval (CorrectF.supportedFinite p) (encodeFinite* xs))
      (Source.eval p xs)
  compiler-correct-finite p xs =
    CorrectF.correctFinite p (representedFinite* xs)
