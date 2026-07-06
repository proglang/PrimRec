{-# OPTIONS --safe #-}

module Core.Instances.Equations.Nat where

open import Data.Vec using (Vec; []; _∷_; map)
open import Data.Nat using (_+_)

import PR-Nat as Source
import Core.Equations.PRFO as CoreEq
open import Core.Instances.Nat
import Core.Instances.Equations.Target as TargetEq

infix 4 _≈ₛ_ _≈ₛ*_

mutual
  data _≈ₛ_ : ∀ {n} → Source.PR n → Source.PR n → Set where
    reflₛ : ∀ {n} {p : Source.PR n} → p ≈ₛ p
    symₛ : ∀ {n} {p q : Source.PR n} → p ≈ₛ q → q ≈ₛ p
    transₛ : ∀ {n} {p q r : Source.PR n} →
      p ≈ₛ q → q ≈ₛ r → p ≈ₛ r
    C-congₛ : ∀ {m n} {f g : Source.PR m}
      {fs gs : Vec (Source.PR n) m} →
      f ≈ₛ g → fs ≈ₛ* gs → Source.C f fs ≈ₛ Source.C g gs
    Pr-congₛ : ∀ {n} {g g′ : Source.PR n}
      {h h′ : Source.PR (2 + n)} →
      g ≈ₛ g′ → h ≈ₛ h′ → Source.Pr g h ≈ₛ Source.Pr g′ h′
    Ct-congₛ : ∀ {n} {g g′ : Source.PR n}
      {h h′ : Source.PR (1 + n)} →
      g ≈ₛ g′ → h ≈ₛ h′ → Source.Ct g h ≈ₛ Source.Ct g′ h′
    Pr-β-zeroₛ : ∀ {m n} (g : Source.PR n) (h : Source.PR (2 + n))
      (parameters : Vec (Source.PR m) n) →
      Source.C (Source.Pr g h) (Source.C Source.Z [] ∷ parameters) ≈ₛ
      Source.C g parameters
    Pr-β-sucₛ : ∀ {m n} (g : Source.PR n) (h : Source.PR (2 + n))
      (counter : Source.PR m) (parameters : Vec (Source.PR m) n) →
      Source.C (Source.Pr g h)
        (Source.C Source.σ (counter ∷ []) ∷ parameters) ≈ₛ
      Source.C h
        (Source.C (Source.Pr g h) (counter ∷ parameters) ∷
         counter ∷ parameters)
    Ct-β-zeroₛ : ∀ {m n} (g : Source.PR n) (h : Source.PR (1 + n))
      (parameters : Vec (Source.PR m) n) →
      Source.C (Source.Ct g h) (Source.C Source.Z [] ∷ parameters) ≈ₛ
      Source.C g parameters
    Ct-β-sucₛ : ∀ {m n} (g : Source.PR n) (h : Source.PR (1 + n))
      (counter : Source.PR m) (parameters : Vec (Source.PR m) n) →
      Source.C (Source.Ct g h)
        (Source.C Source.σ (counter ∷ []) ∷ parameters) ≈ₛ
      Source.C h
        (Source.C (Source.Ct g h) (counter ∷ parameters) ∷ parameters)

  data _≈ₛ*_ : ∀ {m n} →
    Vec (Source.PR n) m → Vec (Source.PR n) m → Set where
    []ₛ : ∀ {n} → _≈ₛ*_ {m = 0} {n = n} [] []
    _∷ₛ_ : ∀ {m n} {p q : Source.PR n}
      {ps qs : Vec (Source.PR n) m} →
      p ≈ₛ q → ps ≈ₛ* qs → (p ∷ ps) ≈ₛ* (q ∷ qs)

preserves : ∀ {n} {p q : Source.PR n} →
  p ≈ₛ q → compile p TargetEq.≈ᴵ compile q
preserves* : ∀ {m n} {ps qs : Vec (Source.PR n) m} →
  ps ≈ₛ* qs → compile* ps TargetEq.≈ᴵ compile* qs

compile*-tuple : ∀ {m n} (ps : Vec (Source.PR n) m) →
  compile* ps TargetEq.≈ᴵ TargetEq.tupleᴾ (map compile ps)
compile*-tuple [] = TargetEq.core CoreEq.≈-refl
compile*-tuple (p ∷ ps) =
  TargetEq.`#-congᴵ (TargetEq.core CoreEq.≈-refl) (compile*-tuple ps)

preserves reflₛ = TargetEq.core CoreEq.≈-refl
preserves (symₛ equation) = TargetEq.symᴵ (preserves equation)
preserves (transₛ first second) =
  TargetEq.transᴵ (preserves first) (preserves second)
preserves (C-congₛ f fs) = TargetEq.C-congᴵ (preserves f) (preserves* fs)
preserves (Pr-congₛ g h) =
  TargetEq.Pr-congᴵ
    (TargetEq.C-congᴵ
      (TargetEq.`case-congᴵ
        (TargetEq.C-congᴵ (preserves g) (TargetEq.core CoreEq.≈-refl))
        (TargetEq.C-congᴵ (preserves h) (TargetEq.core CoreEq.≈-refl)))
      (TargetEq.core CoreEq.≈-refl))
preserves (Ct-congₛ g h) =
  TargetEq.Pr-congᴵ
    (TargetEq.C-congᴵ
      (TargetEq.`case-congᴵ
        (TargetEq.C-congᴵ (preserves g) (TargetEq.core CoreEq.≈-refl))
        (TargetEq.C-congᴵ (preserves h) (TargetEq.core CoreEq.≈-refl)))
      (TargetEq.core CoreEq.≈-refl))
preserves (Pr-β-zeroₛ g h parameters) =
  TargetEq.transᴵ
    (TargetEq.C-congᴵ (TargetEq.core CoreEq.≈-refl)
      (TargetEq.`#-congᴵ (TargetEq.core CoreEq.≈-refl)
        (compile*-tuple parameters)))
    (TargetEq.transᴵ
      (TargetEq.Pr-β-zero (compile g) (compile h) (map compile parameters))
      (TargetEq.C-congᴵ (TargetEq.core CoreEq.≈-refl)
        (TargetEq.symᴵ (compile*-tuple parameters))))
preserves (Pr-β-sucₛ g h counter parameters) =
  TargetEq.transᴵ lhs-to-schema
    (TargetEq.transᴵ
      (TargetEq.Pr-β-suc (compile g) (compile h) (compile counter)
        (map compile parameters))
      (TargetEq.C-congᴵ (TargetEq.core CoreEq.≈-refl)
        (TargetEq.symᴵ arguments-to-schema)))
  where
  parameter-equation = compile*-tuple parameters

  lhs-to-schema =
    TargetEq.C-congᴵ (TargetEq.core CoreEq.≈-refl)
      (TargetEq.`#-congᴵ (TargetEq.core CoreEq.≈-refl)
        parameter-equation)

  result-equation =
    TargetEq.C-congᴵ (TargetEq.core CoreEq.≈-refl)
      (TargetEq.`#-congᴵ (TargetEq.core CoreEq.≈-refl)
        parameter-equation)

  arguments-to-schema =
    TargetEq.`#-congᴵ result-equation
      (TargetEq.`#-congᴵ (TargetEq.core CoreEq.≈-refl)
        parameter-equation)
preserves (Ct-β-zeroₛ g h parameters) =
  TargetEq.transᴵ
    (TargetEq.C-congᴵ (TargetEq.core CoreEq.≈-refl)
      (TargetEq.`#-congᴵ (TargetEq.core CoreEq.≈-refl)
        (compile*-tuple parameters)))
    (TargetEq.transᴵ
      (TargetEq.Ct-β-zero (compile g) (compile h) (map compile parameters))
      (TargetEq.C-congᴵ (TargetEq.core CoreEq.≈-refl)
        (TargetEq.symᴵ (compile*-tuple parameters))))
preserves (Ct-β-sucₛ g h counter parameters) =
  TargetEq.transᴵ lhs-to-schema
    (TargetEq.transᴵ
      (TargetEq.Ct-β-suc (compile g) (compile h) (compile counter)
        (map compile parameters))
      (TargetEq.C-congᴵ (TargetEq.core CoreEq.≈-refl)
        (TargetEq.symᴵ arguments-to-schema)))
  where
  parameter-equation = compile*-tuple parameters

  lhs-to-schema =
    TargetEq.C-congᴵ (TargetEq.core CoreEq.≈-refl)
      (TargetEq.`#-congᴵ (TargetEq.core CoreEq.≈-refl)
        parameter-equation)

  result-equation =
    TargetEq.C-congᴵ (TargetEq.core CoreEq.≈-refl)
      (TargetEq.`#-congᴵ (TargetEq.core CoreEq.≈-refl)
        parameter-equation)

  arguments-to-schema =
    TargetEq.`#-congᴵ result-equation parameter-equation

preserves* []ₛ = TargetEq.core CoreEq.≈-refl
preserves* (p ∷ₛ ps) = TargetEq.`#-congᴵ (preserves p) (preserves* ps)
