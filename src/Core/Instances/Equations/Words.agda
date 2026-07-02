{-# OPTIONS --safe #-}

module Core.Instances.Equations.Words where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; _+_)
open import Data.Vec using (Vec; []; _∷_; map)

import PR-Words as Source
import Core.Finite as Finite
import Relation.Binary.PropositionalEquality as Eq
open import Core.PRFO
import Core.Equations.PRFO as CoreEq
open import Core.Instances.Common
open import Core.Instances.Words
import Core.Instances.Equations.Target as TargetEq

infix 4 _≈ₛ_ _≈ₛ*_ _≈ᵂ_

----------------------------------------------------------------------
-- Source equations
----------------------------------------------------------------------

mutual
  data _≈ₛ_ : ∀ {k n} →
    Source.PR (Fin k) n → Source.PR (Fin k) n → Set where
    reflₛ : ∀ {k n} {p : Source.PR (Fin k) n} → p ≈ₛ p
    symₛ : ∀ {k n} {p q : Source.PR (Fin k) n} →
      p ≈ₛ q → q ≈ₛ p
    transₛ : ∀ {k n} {p q r : Source.PR (Fin k) n} →
      p ≈ₛ q → q ≈ₛ r → p ≈ₛ r
    C-congₛ : ∀ {k m n} {f g : Source.PR (Fin k) m}
      {fs gs : Vec (Source.PR (Fin k) n) m} →
      f ≈ₛ g → fs ≈ₛ* gs → Source.C f fs ≈ₛ Source.C g gs
    P-congₛ : ∀ {k n} {g g′ : Source.PR (Fin k) n}
      {h h′ : Fin k → Source.PR (Fin k) (2 + n)} →
      g ≈ₛ g′ → ((a : Fin k) → h a ≈ₛ h′ a) →
      Source.P g h ≈ₛ Source.P g′ h′
    P-β-emptyₛ : ∀ {k m n} (g : Source.PR (Fin k) n)
      (h : Fin k → Source.PR (Fin k) (2 + n))
      (parameters : Vec (Source.PR (Fin k) m) n) →
      Source.C (Source.P g h) (Source.C Source.Z [] ∷ parameters) ≈ₛ
      Source.C g parameters
    P-β-letterₛ : ∀ {k m n} (g : Source.PR (Fin k) n)
      (h : Fin k → Source.PR (Fin k) (2 + n))
      (a : Fin k) (tail : Source.PR (Fin k) m)
      (parameters : Vec (Source.PR (Fin k) m) n) →
      Source.C (Source.P g h)
        (Source.C (Source.σ a) (tail ∷ []) ∷ parameters) ≈ₛ
      Source.C (h a)
        (Source.C (Source.P g h) (tail ∷ parameters) ∷
         tail ∷ parameters)

  data _≈ₛ*_ : ∀ {k m n} →
    Vec (Source.PR (Fin k) n) m →
    Vec (Source.PR (Fin k) n) m → Set where
    []ₛ : ∀ {k n} → _≈ₛ*_ {k} {m = 0} {n = n} [] []
    _∷ₛ_ : ∀ {k m n} {p q : Source.PR (Fin k) n}
      {ps qs : Vec (Source.PR (Fin k) n) m} →
      p ≈ₛ q → ps ≈ₛ* qs → (p ∷ ps) ≈ₛ* (q ∷ qs)

----------------------------------------------------------------------
-- Target equations for the finite-word representation
----------------------------------------------------------------------

data _≈ᵂ_ : ∀ {T U} → T →ᴾ U → T →ᴾ U → Set where
  coreᵂ : ∀ {T U} {p q : T →ᴾ U} → p TargetEq.≈ᴵ q → p ≈ᵂ q
  symᵂ : ∀ {T U} {p q : T →ᴾ U} → p ≈ᵂ q → q ≈ᵂ p
  transᵂ : ∀ {T U} {p q r : T →ᴾ U} →
    p ≈ᵂ q → q ≈ᵂ r → p ≈ᵂ r
  C-congᵂ : ∀ {T U V} {f g : U →ᴾ V} {p q : T →ᴾ U} →
    f ≈ᵂ g → p ≈ᵂ q → C f p ≈ᵂ C g q
  `#-congᵂ : ∀ {T U V} {f g : T →ᴾ U} {p q : T →ᴾ V} →
    f ≈ᵂ g → p ≈ᵂ q → `# f p ≈ᵂ `# g q
  `case-congᵂ : ∀ {T U V} {f g : T →ᴾ V} {p q : U →ᴾ V} →
    f ≈ᵂ g → p ≈ᵂ q → `case f p ≈ᵂ `case g q
  P-congᵂ : ∀ {G T U} {f g : (G [ T `× ind G ]) `× U →ᴾ T} →
    f ≈ᵂ g →
    P {G = G} {T = T} {U = U} f ≈ᵂ P {G = G} {T = T} {U = U} g

  word-β-emptyᵂ : ∀ {k m n}
    (g : vec (Word k) n →ᴾ Word k)
    (h : Fin k → vec (Word k) (2 + n) →ᴾ Word k)
    (parameters : Vec (vec (Word k) m →ᴾ Word k) n) →
    C (P {G = WordF k} {T = Word k} {U = vec (Word k) n}
         (wordParaHandlerᴾ {k = k} g h))
      (`# (C (emptyCon {k}) `⊤) (TargetEq.tupleᴾ parameters)) ≈ᵂ
    C g (TargetEq.tupleᴾ parameters)

  word-β-letterᵂ : ∀ {k m n}
    (g : vec (Word k) n →ᴾ Word k)
    (h : Fin k → vec (Word k) (2 + n) →ᴾ Word k)
    (a : Fin k) (tail : vec (Word k) m →ᴾ Word k)
    (parameters : Vec (vec (Word k) m →ᴾ Word k) n) →
    C (P {G = WordF k} {T = Word k} {U = vec (Word k) n}
         (wordParaHandlerᴾ {k = k} g h))
      (`# (C (letterCon {k = k} a) (`# tail `⊤))
          (TargetEq.tupleᴾ parameters)) ≈ᵂ
    C (h a)
      (`# (C (P {G = WordF k} {T = Word k} {U = vec (Word k) n}
                  (wordParaHandlerᴾ {k = k} g h))
             (`# tail (TargetEq.tupleᴾ parameters)))
          (`# tail (TargetEq.tupleᴾ parameters)))

reflᵂ : ∀ {T U} {p : T →ᴾ U} → p ≈ᵂ p
reflᵂ = coreᵂ (TargetEq.core CoreEq.≈-refl)

caseLetters-congᵂ : ∀ {k T U V}
  {hs ks : (a : Fin k) → vec T 1 `× U →ᴾ V} →
  ((a : Fin k) → hs a ≈ᵂ ks a) →
  caseLettersAt hs ≈ᵂ caseLettersAt ks
caseLetters-congᵂ {zero} pointwise = C-congᵂ reflᵂ reflᵂ
caseLetters-congᵂ {Data.Nat.suc k} pointwise =
  C-congᵂ
    (`case-congᵂ (pointwise Data.Fin.zero)
      (caseLetters-congᵂ (λ a → pointwise (Data.Fin.suc a))))
    reflᵂ

wordParaHandler-congᵂ : ∀ {k n}
  {g g′ : vec (Word k) n →ᴾ Word k}
  {h h′ : Fin k → vec (Word k) (2 + n) →ᴾ Word k} →
  g ≈ᵂ g′ → ((a : Fin k) → h a ≈ᵂ h′ a) →
  wordParaHandlerᴾ g h ≈ᵂ wordParaHandlerᴾ g′ h′
wordParaHandler-congᵂ g≈g′ h≈h′ =
  C-congᵂ
    (`case-congᵂ (C-congᵂ g≈g′ reflᵂ)
      (caseLetters-congᵂ λ a → C-congᵂ (h≈h′ a) reflᵂ))
    reflᵂ

----------------------------------------------------------------------
-- Preservation
----------------------------------------------------------------------

preserves : ∀ {k n} {p q : Source.PR (Fin k) n} →
  p ≈ₛ q → compile p ≈ᵂ compile q
preserves* : ∀ {k m n}
  {ps qs : Vec (Source.PR (Fin k) n) m} →
  ps ≈ₛ* qs → compile* ps ≈ᵂ compile* qs

compile*-tuple : ∀ {k m n}
  (ps : Vec (Source.PR (Fin k) n) m) →
  compile* ps ≈ᵂ TargetEq.tupleᴾ (map compile ps)
compile*-tuple [] = reflᵂ
compile*-tuple (p ∷ ps) = `#-congᵂ reflᵂ (compile*-tuple ps)

preserves reflₛ = reflᵂ
preserves (symₛ equation) = symᵂ (preserves equation)
preserves (transₛ first second) = transᵂ (preserves first) (preserves second)
preserves (C-congₛ f fs) = C-congᵂ (preserves f) (preserves* fs)
preserves (P-congₛ g≈g′ h≈h′) =
  P-congᵂ (wordParaHandler-congᵂ (preserves g≈g′)
    (λ a → preserves (h≈h′ a)))
preserves (P-β-emptyₛ g h parameters) =
  transᵂ
    (C-congᵂ reflᵂ (`#-congᵂ reflᵂ (compile*-tuple parameters)))
    (transᵂ
      (word-β-emptyᵂ (compile g) (λ a → compile (h a))
        (map compile parameters))
      (C-congᵂ reflᵂ (symᵂ (compile*-tuple parameters))))
preserves (P-β-letterₛ g h a tail parameters) =
  transᵂ lhs-to-schema
    (transᵂ
      (word-β-letterᵂ (compile g) (λ i → compile (h i)) a
        (compile tail) (map compile parameters))
      (C-congᵂ reflᵂ (symᵂ arguments-to-schema)))
  where
  parameter-equation = compile*-tuple parameters
  lhs-to-schema =
    C-congᵂ reflᵂ (`#-congᵂ reflᵂ parameter-equation)
  result-equation =
    C-congᵂ reflᵂ (`#-congᵂ reflᵂ parameter-equation)
  arguments-to-schema =
    `#-congᵂ result-equation (`#-congᵂ reflᵂ parameter-equation)

preserves* []ₛ = reflᵂ
preserves* (p ∷ₛ ps) = `#-congᵂ (preserves p) (preserves* ps)

----------------------------------------------------------------------
-- Equation preservation for an arbitrary finitely presented alphabet
----------------------------------------------------------------------

module ForFinite {A : Set} (finiteA : Finite.Finite A) where
  module W = Core.Instances.Words.For finiteA

  k = Finite.size finiteA

  infix 4 _≈F_ _≈F*_

  mutual
    data _≈F_ : ∀ {n} → Source.PR A n → Source.PR A n → Set where
      reflF : ∀ {n} {p : Source.PR A n} → p ≈F p
      symF : ∀ {n} {p q : Source.PR A n} → p ≈F q → q ≈F p
      transF : ∀ {n} {p q r : Source.PR A n} →
        p ≈F q → q ≈F r → p ≈F r
      C-congF : ∀ {m n} {f g : Source.PR A m}
        {fs gs : Vec (Source.PR A n) m} →
        f ≈F g → fs ≈F* gs → Source.C f fs ≈F Source.C g gs
      P-congF : ∀ {n} {g g′ : Source.PR A n}
        {h h′ : A → Source.PR A (2 + n)} →
        g ≈F g′ → ((a : A) → h a ≈F h′ a) →
        Source.P g h ≈F Source.P g′ h′
      P-β-emptyF : ∀ {m n} (g : Source.PR A n)
        (h : A → Source.PR A (2 + n))
        (parameters : Vec (Source.PR A m) n) →
        Source.C (Source.P g h) (Source.C Source.Z [] ∷ parameters) ≈F
        Source.C g parameters
      P-β-letterF : ∀ {m n} (g : Source.PR A n)
        (h : A → Source.PR A (2 + n))
        (a : A) (tail : Source.PR A m)
        (parameters : Vec (Source.PR A m) n) →
        Source.C (Source.P g h)
          (Source.C (Source.σ a) (tail ∷ []) ∷ parameters) ≈F
        Source.C (h a)
          (Source.C (Source.P g h) (tail ∷ parameters) ∷
           tail ∷ parameters)

    data _≈F*_ : ∀ {m n} →
      Vec (Source.PR A n) m → Vec (Source.PR A n) m → Set where
      []F : ∀ {n} → _≈F*_ {m = 0} {n = n} [] []
      _∷F_ : ∀ {m n} {p q : Source.PR A n}
        {ps qs : Vec (Source.PR A n) m} →
        p ≈F q → ps ≈F* qs → (p ∷ ps) ≈F* (q ∷ qs)

  preservesFinite : ∀ {n} {p q : Source.PR A n} →
    p ≈F q → W.compileFinite p ≈ᵂ W.compileFinite q
  preservesFinite* : ∀ {m n}
    {ps qs : Vec (Source.PR A n) m} →
    ps ≈F* qs → W.compileFinite* ps ≈ᵂ W.compileFinite* qs

  compileFinite*-tuple : ∀ {m n} (ps : Vec (Source.PR A n) m) →
    W.compileFinite* ps ≈ᵂ TargetEq.tupleᴾ (map W.compileFinite ps)
  compileFinite*-tuple [] = reflᵂ
  compileFinite*-tuple (p ∷ ps) =
    `#-congᵂ reflᵂ (compileFinite*-tuple ps)

  decode-compile : ∀ {n} (h : A → Source.PR A n) (a : A) →
    W.compileFinite (h (Finite.decode finiteA (Finite.encode finiteA a))) ≈ᵂ
    W.compileFinite (h a)
  decode-compile h a =
    Eq.subst
      (λ b → W.compileFinite
          (h (Finite.decode finiteA (Finite.encode finiteA a))) ≈ᵂ
        W.compileFinite (h b))
      (Finite.decode-encode finiteA a)
      reflᵂ

  preservesFinite reflF = reflᵂ
  preservesFinite (symF equation) = symᵂ (preservesFinite equation)
  preservesFinite (transF first second) =
    transᵂ (preservesFinite first) (preservesFinite second)
  preservesFinite (C-congF f fs) =
    C-congᵂ (preservesFinite f) (preservesFinite* fs)
  preservesFinite (P-congF g≈g′ h≈h′) =
    P-congᵂ
      (wordParaHandler-congᵂ (preservesFinite g≈g′)
        (λ i → preservesFinite (h≈h′ (Finite.decode finiteA i))))
  preservesFinite (P-β-emptyF g h parameters) =
    transᵂ
      (C-congᵂ reflᵂ
        (`#-congᵂ reflᵂ (compileFinite*-tuple parameters)))
      (transᵂ
        (word-β-emptyᵂ (W.compileFinite g)
          (λ i → W.compileFinite (h (Finite.decode finiteA i)))
          (map W.compileFinite parameters))
        (C-congᵂ reflᵂ (symᵂ (compileFinite*-tuple parameters))))
  preservesFinite (P-β-letterF g h a tail parameters) =
    transᵂ lhs-to-schema
      (transᵂ
        (word-β-letterᵂ (W.compileFinite g)
          (λ i → W.compileFinite (h (Finite.decode finiteA i)))
          (Finite.encode finiteA a) (W.compileFinite tail)
          (map W.compileFinite parameters))
        (transᵂ
          (C-congᵂ reflᵂ (symᵂ arguments-to-schema))
          (C-congᵂ (decode-compile h a) reflᵂ)))
    where
    parameter-equation = compileFinite*-tuple parameters
    lhs-to-schema =
      C-congᵂ reflᵂ (`#-congᵂ reflᵂ parameter-equation)
    result-equation =
      C-congᵂ reflᵂ (`#-congᵂ reflᵂ parameter-equation)
    arguments-to-schema =
      `#-congᵂ result-equation (`#-congᵂ reflᵂ parameter-equation)

  preservesFinite* []F = reflᵂ
  preservesFinite* (p ∷F ps) =
    `#-congᵂ (preservesFinite p) (preservesFinite* ps)
