{-# OPTIONS --safe #-}

module Core.Instances.Words where

open import Data.Bool using (_∧_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec using (Vec; []; _∷_; lookup; replicate)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

import PR-Words as Source
open import Core.PRFO
open import Core.Finite
open import Core.Instances.Common
import Core.Instances.Model as InstanceModel
open import Core.Semantics.Types using (Guarded; WellFormed; Polynomial)
import Core.Models.PRFO as Model

-- An alphabet of size k is represented by Fin k.  The empty-word branch is
-- followed by one unary constructor for every letter.
WordRanks : (k : ℕ) → Vec ℕ (suc k)
WordRanks k = zero ∷ replicate k 1

letter-rank : ∀ {k} (a : Fin k) → lookup (WordRanks k) (suc a) ≡ 1
letter-rank {suc k} zero = refl
letter-rank {suc k} (suc a) = letter-rank a

letter-arity : ∀ {k n} (a : Fin k) →
  (lookup (WordRanks k) (suc a) + lookup (WordRanks k) (suc a)) + n ≡ 2 + n
letter-arity a rewrite letter-rank a = refl

LetterF : ℕ → Ty FO 1
LetterF zero = `𝟘
LetterF (suc k) = vec (` zero) 1 `+ LetterF k

WordF : ℕ → Ty FO 1
WordF k = `𝟙 `+ LetterF k

Word : ℕ → TY FO
Word k = ind (WordF k)

LetterF-as-Branches : (k : ℕ) →
  LetterF k ≡ Branches (replicate k 1)
LetterF-as-Branches zero = refl
LetterF-as-Branches (suc k) =
  cong (vec (` zero) 1 `+_) (LetterF-as-Branches k)

WordF-as-Branches : (k : ℕ) → WordF k ≡ Branches (WordRanks k)
WordF-as-Branches k = cong (`𝟙 `+_) (LetterF-as-Branches k)

Word-as-Tree : (k : ℕ) → Word k ≡ Tree (WordRanks k)
Word-as-Tree k = cong ind (WordF-as-Branches k)

WordF-guarded : (k : ℕ) → Guarded (WordF k)
WordF-guarded k = refl

LetterF-wellFormed : (k : ℕ) → WellFormed (LetterF k)
LetterF-wellFormed zero = refl
LetterF-wellFormed (suc k) =
  cong₂ _∧_ refl (LetterF-wellFormed k)

WordF-wellFormed : (k : ℕ) → WellFormed (WordF k)
WordF-wellFormed k = cong₂ _∧_ refl (LetterF-wellFormed k)

WordF-polynomial : (k : ℕ) → Polynomial (WordF k)
WordF-polynomial k = Core.Semantics.Types.fo-polynomial (WordF k)

Word-wellFormed : (k : ℕ) → WellFormed (Word k)
Word-wellFormed k =
  cong₂ _∧_ (WordF-guarded k) (WordF-wellFormed k)

Word-polynomial : (k : ℕ) → Polynomial (Word k)
Word-polynomial k = Core.Semantics.Types.fo-polynomial (Word k)

letterSymbol : ∀ {k} → Fin k → Fin (suc k)
letterSymbol = suc

emptyCon : ∀ {k} → vec (Word k) 0 →ᴾ Word k
emptyCon = C fold ι₁

injectLetterAt : ∀ {k T} (a : Fin k) →
  vec T 1 →ᴾ LetterF k ⇐ T
injectLetterAt {suc k} zero = ι₁
injectLetterAt {suc k} (suc a) = C ι₂ (injectLetterAt a)

injectLetter : ∀ {k T} (a : Fin k) →
  vec T 1 →ᴾ WordF k ⇐ T
injectLetter a = C ι₂ (injectLetterAt a)

letterCon : ∀ {k} (a : Fin k) → vec (Word k) 1 →ᴾ Word k
letterCon {k} a = C fold (injectLetter a)

caseLettersAt : ∀ {k T U V} →
  ((a : Fin k) → vec T 1 `× U →ᴾ V) →
  (LetterF k ⇐ T) `× U →ᴾ V
caseLettersAt {zero} handlers = C `⊥ π₁
caseLettersAt {suc k} handlers =
  C (`case (handlers zero) (caseLettersAt (λ a → handlers (suc a))))
    dist-+-×

wordParaHandlerᴾ : ∀ {k n} →
  (vec (Word k) n →ᴾ Word k) →
  (Fin k → vec (Word k) (2 + n) →ᴾ Word k) →
  (WordF k ⇐ (Word k `× Word k)) `× vec (Word k) n →ᴾ Word k
wordParaHandlerᴾ {k} {n} g h =
  C (`case (C g π₂)
           (caseLettersAt λ a → C (h a) (preparePara 1 n)))
    dist-+-×

compile : ∀ {k n} → Source.PR (Fin k) n → vec (Word k) n →ᴾ Word k
compile* : ∀ {k m n} → Vec (Source.PR (Fin k) n) m →
           vec (Word k) n →ᴾ vec (Word k) m
wordParaHandler : ∀ {k n} → Source.PR (Fin k) n →
  (Fin k → Source.PR (Fin k) (2 + n)) →
  (WordF k ⇐ (Word k `× Word k)) `× vec (Word k) n →ᴾ
  Word k

compile Source.Z = emptyCon
compile (Source.σ a) = letterCon a
compile (Source.π i) = lookupᴾ i
compile (Source.C f fs) = C (compile f) (compile* fs)
compile {k} {suc n} (Source.P g h) =
  P (wordParaHandler g h)

compile* []       = `⊤
compile* (p ∷ ps) = `# (compile p) (compile* ps)

wordParaHandler g h =
  wordParaHandlerᴾ (compile g) (λ a → compile (h a))

compile-typed : ∀ {k n} → Source.PR (Fin k) n → Set
compile-typed {k} {n} p = vec (Word k) n →ᴾ Word k

typed : ∀ {k n} (p : Source.PR (Fin k) n) → compile-typed p
typed = compile

----------------------------------------------------------------------
-- Arbitrary finite alphabets
----------------------------------------------------------------------

module For {A : Set} (finiteA : Finite A) where
  Target : TY FO
  Target = Word (size finiteA)

  compileFinite : ∀ {n} → Source.PR A n → vec Target n →ᴾ Target
  compileFinite* : ∀ {m n} → Vec (Source.PR A n) m →
    vec Target n →ᴾ vec Target m
  finiteHandler : ∀ {n} → Source.PR A n →
    (A → Source.PR A (2 + n)) →
    (WordF (size finiteA) ⇐ (Target `× Target)) `× vec Target n →ᴾ Target

  compileFinite Source.Z = emptyCon
  compileFinite (Source.σ a) = letterCon (encode finiteA a)
  compileFinite (Source.π i) = lookupᴾ i
  compileFinite (Source.C f fs) = C (compileFinite f) (compileFinite* fs)
  compileFinite (Source.P g h) = P (finiteHandler g h)

  compileFinite* [] = `⊤
  compileFinite* (p ∷ ps) = `# (compileFinite p) (compileFinite* ps)

  finiteHandler g h =
    wordParaHandlerᴾ (compileFinite g)
      (λ i → compileFinite (h (decode finiteA i)))

  typedFinite : ∀ {n} (p : Source.PR A n) →
    vec Target n →ᴾ Target
  typedFinite = compileFinite

  module Semantics {ℓ : Level} (M : Model.Model ℓ) where
    open Model.Model M
    open InstanceModel.For M

    denote : ∀ {n} → Source.PR A n → vec Target n ⇒ᴹ Target
    denote* : ∀ {m n} → Vec (Source.PR A n) m →
      vec Target n ⇒ᴹ vec Target m

    denote Source.Z = Model.interpret structure (compileFinite Source.Z)
    denote (Source.σ a) =
      Model.interpret structure (compileFinite (Source.σ a))
    denote (Source.π i) = Model.interpret structure (lookupᴾ i)
    denote (Source.C f fs) = Cᴹ (denote f) (denote* fs)
    denote (Source.P g h) =
      Pᴹ (Model.interpret structure (finiteHandler g h))

    denote* [] = ⊤ᴹ
    denote* (p ∷ ps) = pairᴹ (denote p) (denote* ps)

    preserves : ∀ {n} (p : Source.PR A n) →
      Model.interpret structure (compileFinite p) ≈ᴹ denote p
    preserves* : ∀ {m n} (ps : Vec (Source.PR A n) m) →
      Model.interpret structure (compileFinite* ps) ≈ᴹ denote* ps

    preserves Source.Z = ≈-reflᴹ
    preserves (Source.σ a) = ≈-reflᴹ
    preserves (Source.π i) = ≈-reflᴹ
    preserves (Source.C f fs) = C-congᴹ (preserves f) (preserves* fs)
    preserves (Source.P g h) = P-congᴹ ≈-reflᴹ

    preserves* [] = ≈-reflᴹ
    preserves* (p ∷ ps) = pair-congᴹ (preserves p) (preserves* ps)

----------------------------------------------------------------------
-- Categorical source semantics and preservation
----------------------------------------------------------------------

module Semantics {ℓ : Level} (M : Model.Model ℓ) where
  open Model.Model M
  open InstanceModel.For M

  denote : ∀ {k n} → Source.PR (Fin k) n →
    vec (Word k) n ⇒ᴹ Word k
  denote* : ∀ {k m n} → Vec (Source.PR (Fin k) n) m →
    vec (Word k) n ⇒ᴹ vec (Word k) m

  denote Source.Z = Model.interpret structure (compile Source.Z)
  denote (Source.σ a) = Model.interpret structure (compile (Source.σ a))
  denote (Source.π i) = Model.interpret structure (lookupᴾ i)
  denote (Source.C f fs) = Cᴹ (denote f) (denote* fs)
  denote {k} {suc n} (Source.P g h) =
    Pᴹ (Model.interpret structure (wordParaHandler g h))

  denote* []       = ⊤ᴹ
  denote* (p ∷ ps) = pairᴹ (denote p) (denote* ps)

  preserves : ∀ {k n} (p : Source.PR (Fin k) n) →
              Model.interpret structure (compile p) ≈ᴹ denote p
  preserves* : ∀ {k m n} (ps : Vec (Source.PR (Fin k) n) m) →
               Model.interpret structure (compile* ps) ≈ᴹ denote* ps

  preserves Source.Z = ≈-reflᴹ
  preserves (Source.σ a) = ≈-reflᴹ
  preserves (Source.π i) = ≈-reflᴹ
  preserves (Source.C f fs) = C-congᴹ (preserves f) (preserves* fs)
  preserves {k} {suc n} (Source.P g h) = P-congᴹ ≈-reflᴹ

  preserves* [] = ≈-reflᴹ
  preserves* (p ∷ ps) = pair-congᴹ (preserves p) (preserves* ps)

  infix 4 _≈Source_
  _≈Source_ : ∀ {k n} →
    Source.PR (Fin k) n → Source.PR (Fin k) n → Set ℓ
  p ≈Source q = denote p ≈ᴹ denote q

  equations-preserved : ∀ {k n} {p q : Source.PR (Fin k) n} →
    p ≈Source q →
    Model.interpret structure (compile p) ≈ᴹ Model.interpret structure (compile q)
  equations-preserved {p = p} {q = q} equation =
    ≈-transᴹ (preserves p) (≈-transᴹ equation (≈-symᴹ (preserves q)))
