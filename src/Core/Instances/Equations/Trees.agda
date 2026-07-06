{-# OPTIONS --safe #-}

module Core.Instances.Equations.Trees where

open import Data.Fin using (Fin)
open import Data.Nat using (_+_)
open import Data.Vec using (Vec; []; _∷_; _++_; map)

import Core.Equations.PRFO as CoreEq
open import Core.PRFO using (C; `#)
open import Core.Instances.Trees
import Core.Instances.Equations.Target as TargetEq
import Core.Instances.Source.Trees as Source

infix 4 _≈ₛ_ _≈ₛ*_

mutual
  data _≈ₛ_ {R : Source.Ranked} : ∀ {n} →
    Source.PR R n → Source.PR R n → Set where
    reflₛ : ∀ {n} {p : Source.PR R n} → p ≈ₛ p
    symₛ : ∀ {n} {p q : Source.PR R n} → p ≈ₛ q → q ≈ₛ p
    transₛ : ∀ {n} {p q r : Source.PR R n} →
      p ≈ₛ q → q ≈ₛ r → p ≈ₛ r
    C-congₛ : ∀ {m n} {f g : Source.PR R m}
      {fs gs : Vec (Source.PR R n) m} →
      f ≈ₛ g → fs ≈ₛ* gs → Source.C f fs ≈ₛ Source.C g gs
    Pr-congₛ : ∀ {n}
      {hs ks : (a : Fin (Source.count R)) →
        Source.PR R ((Source.rank R a + Source.rank R a) + n)} →
      ((a : Fin (Source.count R)) → hs a ≈ₛ ks a) →
      Source.Pr hs ≈ₛ Source.Pr ks
    Pr-βₛ : ∀ {m n}
      (steps : (a : Fin (Source.count R)) →
        Source.PR R ((Source.rank R a + Source.rank R a) + n))
      (a : Fin (Source.count R))
      (children : Vec (Source.PR R m) (Source.rank R a))
      (parameters : Vec (Source.PR R m) n) →
      Source.C (Source.Pr steps)
        (Source.C (Source.σ a) children ∷ parameters) ≈ₛ
      Source.C (steps a)
        ((map (λ child → Source.C (Source.Pr steps) (child ∷ parameters))
            children ++ children) ++ parameters)

  data _≈ₛ*_ {R : Source.Ranked} : ∀ {m n} →
    Vec (Source.PR R n) m → Vec (Source.PR R n) m → Set where
    []ₛ : ∀ {n} → _≈ₛ*_ {R = R} {m = 0} {n = n} [] []
    _∷ₛ_ : ∀ {m n} {p q : Source.PR R n}
      {ps qs : Vec (Source.PR R n) m} →
      p ≈ₛ q → ps ≈ₛ* qs → (p ∷ ps) ≈ₛ* (q ∷ qs)

preserves : ∀ {R n} {p q : Source.PR R n} →
  p ≈ₛ q → compile p TargetEq.≈ᴵ compile q
preserves* : ∀ {R m n} {ps qs : Vec (Source.PR R n) m} →
  ps ≈ₛ* qs → compile* ps TargetEq.≈ᴵ compile* qs

compile*-tuple : ∀ {R m n} (ps : Vec (Source.PR R n) m) →
  compile* ps TargetEq.≈ᴵ TargetEq.tupleᴾ (map compile ps)
compile*-tuple [] = TargetEq.core CoreEq.≈-refl
compile*-tuple (p ∷ ps) =
  TargetEq.`#-congᴵ (TargetEq.core CoreEq.≈-refl) (compile*-tuple ps)

preserves reflₛ = TargetEq.core CoreEq.≈-refl
preserves (symₛ equation) = TargetEq.symᴵ (preserves equation)
preserves (transₛ first second) =
  TargetEq.transᴵ (preserves first) (preserves second)
preserves (C-congₛ f fs) = TargetEq.C-congᴵ (preserves f) (preserves* fs)
preserves {R} (Pr-congₛ pointwise) =
  TargetEq.Pr-congᴵ
    (TargetEq.paraHandler-congᴵ (Source.ranks R)
      (λ i → preserves (pointwise i)))

preserves {R} (Pr-βₛ {m = m} {n = n} steps a children parameters) =
  TargetEq.transᴵ lhs-to-schema
    (TargetEq.transᴵ
      (TargetEq.Pr-β-branch (Source.ranks R) (λ i → compile (steps i))
        a (map compile children) (map compile parameters))
      (TargetEq.C-congᴵ (TargetEq.core CoreEq.≈-refl)
        (TargetEq.symᴵ arguments-to-schema)))
  where
  parameter-equation = compile*-tuple parameters
  child-equation = compile*-tuple children

  lhs-to-schema =
    TargetEq.C-congᴵ (TargetEq.core CoreEq.≈-refl)
      (TargetEq.`#-congᴵ
        (TargetEq.C-congᴵ (TargetEq.core CoreEq.≈-refl) child-equation)
        parameter-equation)

  result-equation : (child : Source.PR R m) →
    compile (Source.C (Source.Pr steps) (child ∷ parameters)) TargetEq.≈ᴵ
    C (compile (Source.Pr steps))
      (`# (compile child) (TargetEq.tupleᴾ (map compile parameters)))
  result-equation child =
    TargetEq.C-congᴵ (TargetEq.core CoreEq.≈-refl)
      (TargetEq.`#-congᴵ (TargetEq.core CoreEq.≈-refl)
        parameter-equation)

  plain-prefix : ∀ {r} (xs : Vec (Source.PR R m) r) →
    compile* (xs ++ parameters) TargetEq.≈ᴵ
    TargetEq.tupleᴾ (map compile xs ++ map compile parameters)
  plain-prefix [] = parameter-equation
  plain-prefix (x ∷ xs) =
    TargetEq.`#-congᴵ (TargetEq.core CoreEq.≈-refl) (plain-prefix xs)

  results-prefix : ∀ {r s} (xs : Vec (Source.PR R m) r)
    (originals : Vec (Source.PR R m) s) →
    compile*
      ((map (λ child → Source.C (Source.Pr steps) (child ∷ parameters)) xs ++
        originals) ++ parameters)
      TargetEq.≈ᴵ
    TargetEq.tupleᴾ
      ((map
        (λ child → C (compile (Source.Pr steps))
          (`# child (TargetEq.tupleᴾ (map compile parameters))))
        (map compile xs) ++ map compile originals) ++
       map compile parameters)
  results-prefix [] originals = plain-prefix originals
  results-prefix (x ∷ xs) originals =
    TargetEq.`#-congᴵ (result-equation x) (results-prefix xs originals)

  arguments-to-schema = results-prefix children children

preserves* []ₛ = TargetEq.core CoreEq.≈-refl
preserves* (p ∷ₛ ps) = TargetEq.`#-congᴵ (preserves p) (preserves* ps)
