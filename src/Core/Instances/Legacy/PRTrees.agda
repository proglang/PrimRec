module Core.Instances.Legacy.PRTrees where

-- Compatibility with the original development.  This module is deliberately
-- not part of the --safe Core aggregate: PR-Trees uses TERMINATING for its
-- evaluator.  The bridge itself adds no postulates.

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; tabulate)
open import Data.Vec.Properties using
  (lookup-map; lookup∘tabulate; map-++; map-∘; tabulate∘lookup;
   tabulate-∘; tabulate-cong)
open import Function using (_∘_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using
  (_≡_; refl; sym; trans; cong; cong₂)
open Eq.≡-Reasoning

import PR-Trees as Legacy
import Core.Instances.Source.Trees as Source
open import Core.Instances.Legacy.Finite
open import Core.PRFO using (_→ᴾ_)
open import Core.Instances.Common using (vec)
import Core.Instances.Trees as CoreTrees

------------------------------------------------------------------------
-- Signatures, terms, and programs
------------------------------------------------------------------------

signature : Source.Ranked → Legacy.Ranked
signature R = Legacy.mkRanked (Source.rank R)

-- Legacy signatures allow arbitrary symbol sets.  A reverse bridge into Core
-- therefore requires this explicit finiteness witness.
record FiniteSignature (R : Legacy.Ranked) : Set where
  constructor finiteSignature
  field
    symbols-finite : Finite (Legacy.symbols R)

open FiniteSignature public

sourceSignature : (R : Legacy.Ranked) → FiniteSignature R → Source.Ranked
sourceSignature R finiteR = Source.ranked
  (tabulate (λ i → Legacy.rank R (decode (symbols-finite finiteR) i)))

source-rank-decode : ∀ {R} (finiteR : FiniteSignature R)
  (i : Fin (size (symbols-finite finiteR))) →
  Source.rank (sourceSignature R finiteR) i ≡
  Legacy.rank R (decode (symbols-finite finiteR) i)
source-rank-decode finiteR i = lookup∘tabulate _ i

source-rank-encode : ∀ {R} (finiteR : FiniteSignature R)
  (a : Legacy.symbols R) →
  Source.rank (sourceSignature R finiteR)
    (encode (symbols-finite finiteR) a) ≡ Legacy.rank R a
source-rank-encode {R} finiteR a =
  trans
    (source-rank-decode finiteR (encode (symbols-finite finiteR) a))
    (cong (Legacy.rank R)
      (decode-encode (symbols-finite finiteR) a))

signature-finite : (R : Source.Ranked) → FiniteSignature (signature R)
signature-finite R = finiteSignature (finiteFin (Source.count R))

-- Reverse bridge for genuinely finite legacy signatures.  Index transports
-- are confined to constructor arities; composition and recursion remain
-- structural.
fromLegacyProgram : ∀ {R n} (finiteR : FiniteSignature R) →
  Legacy.PR R n → Source.PR (sourceSignature R finiteR) n
fromLegacyPrograms : ∀ {R m n} (finiteR : FiniteSignature R) →
  Vec (Legacy.PR R n) m → Vec (Source.PR (sourceSignature R finiteR) n) m

fromLegacyProgram finiteR (Legacy.σ a) =
  Eq.subst (Source.PR (sourceSignature _ finiteR))
    (source-rank-encode finiteR a)
    (Source.σ (encode (symbols-finite finiteR) a))
fromLegacyProgram finiteR (Legacy.π i) = Source.π i
fromLegacyProgram finiteR (Legacy.C f fs) =
  Source.C (fromLegacyProgram finiteR f) (fromLegacyPrograms finiteR fs)
fromLegacyProgram {n = suc n} finiteR (Legacy.P steps) =
  Source.P λ i →
    Eq.subst (Source.PR (sourceSignature _ finiteR))
      (sym (cong (λ r → (r Data.Nat.+ r) Data.Nat.+ n)
        (source-rank-decode finiteR i)))
      (fromLegacyProgram finiteR
        (steps (decode (symbols-finite finiteR) i)))

fromLegacyPrograms finiteR [] = []
fromLegacyPrograms finiteR (p ∷ ps) =
  fromLegacyProgram finiteR p ∷ fromLegacyPrograms finiteR ps

compileLegacy : ∀ {R n} (finiteR : FiniteSignature R) →
  Legacy.PR R n →
  vec (CoreTrees.Target (sourceSignature R finiteR)) n →ᴾ
  CoreTrees.Target (sourceSignature R finiteR)
compileLegacy finiteR p = CoreTrees.compile (fromLegacyProgram finiteR p)

term : ∀ {R} → Source.Term R → Legacy.Term (signature R)
term {R} (Source.con a children) =
  Legacy.con a (tabulate (λ i → term (children i)))

terms : ∀ {R n} → Vec (Source.Term R) n → Vec (Legacy.Term (signature R)) n
terms = map term

program : ∀ {R n} → Source.PR R n → Legacy.PR (signature R) n
programs : ∀ {R m n} → Vec (Source.PR R n) m →
  Vec (Legacy.PR (signature R) n) m

program (Source.σ a) = Legacy.σ a
program (Source.π i) = Legacy.π i
program (Source.C f fs) = Legacy.C (program f) (programs fs)
program (Source.P steps) = Legacy.P (λ a → program (steps a))

programs [] = []
programs (p ∷ ps) = program p ∷ programs ps

------------------------------------------------------------------------
-- Structural compatibility lemmas
------------------------------------------------------------------------

terms-++ : ∀ {R m n} (xs : Vec (Source.Term R) m)
  (ys : Vec (Source.Term R) n) →
  terms (xs ++ ys) ≡ terms xs ++ terms ys
terms-++ = map-++ term

term-lookup : ∀ {R n} (i : Fin n) (xs : Vec (Source.Term R) n) →
  term (lookup xs i) ≡ lookup (terms xs) i
term-lookup i xs = sym (lookup-map i term xs)

terms-tabulate-lookup : ∀ {R n} (xs : Vec (Source.Term R) n) →
  tabulate (λ i → term (lookup xs i)) ≡ terms xs
terms-tabulate-lookup xs =
  trans
    (tabulate-cong (λ i → sym (lookup-map i term xs)))
    (tabulate∘lookup (terms xs))

------------------------------------------------------------------------
-- The legacy and Core-source evaluators commute
------------------------------------------------------------------------

sound : ∀ {R n} (p : Source.PR R n) (xs : Vec (Source.Term R) n) →
  term (Source.eval p xs) ≡ Legacy.eval (program p) (terms xs)
sound* : ∀ {R m n} (ps : Vec (Source.PR R n) m)
  (xs : Vec (Source.Term R) n) →
  terms (Source.eval* ps xs) ≡ Legacy.eval* (programs ps) (terms xs)

sound (Source.σ a) xs = cong (Legacy.con a) (terms-tabulate-lookup xs)
sound (Source.π i) xs = term-lookup i xs
sound (Source.C f fs) xs =
  trans (sound f (Source.eval* fs xs))
        (cong (Legacy.eval (program f)) (sound* fs xs))
sound {R} {suc n} (Source.P steps) (tree ∷ parameters) = go tree
  where
  legacyP : Legacy.PR (signature R) (suc n)
  legacyP = Legacy.P (λ a → program (steps a))

  go : (tree : Source.Term R) →
    term (Source.eval (Source.P steps) (tree ∷ parameters)) ≡
    Legacy.eval legacyP (term tree ∷ terms parameters)
  go (Source.con a children) =
    trans (sound (steps a) sourceArguments)
          (cong (Legacy.eval (program (steps a))) arguments-sound)
    where
    pairs = tabulate
      (λ i → Source.eval (Source.P steps) (children i ∷ parameters) , children i)

    sourceArguments =
      (map proj₁ pairs ++ map proj₂ pairs) ++ parameters

    legacyChildren = tabulate (λ i → term (children i))

    legacyResults = map
      (λ child → Legacy.eval legacyP (child ∷ terms parameters))
      legacyChildren

    results-sound : terms (map proj₁ pairs) ≡ legacyResults
    results-sound =
      begin
        map term (map proj₁ pairs)
      ≡⟨ sym (map-∘ term proj₁ pairs) ⟩
        map (term ∘ proj₁) pairs
      ≡⟨ sym (tabulate-∘ (term ∘ proj₁)
            (λ i → Source.eval (Source.P steps) (children i ∷ parameters) ,
                   children i)) ⟩
        tabulate
          (λ i → term (Source.eval (Source.P steps)
                            (children i ∷ parameters)))
      ≡⟨ tabulate-cong (λ i → go (children i)) ⟩
        tabulate
          (λ i → Legacy.eval legacyP
                    (term (children i) ∷ terms parameters))
      ≡⟨ tabulate-∘
            (λ child → Legacy.eval legacyP (child ∷ terms parameters))
            (λ i → term (children i)) ⟩
        legacyResults
      ∎

    originals-sound : terms (map proj₂ pairs) ≡ legacyChildren
    originals-sound =
      begin
        map term (map proj₂ pairs)
      ≡⟨ sym (map-∘ term proj₂ pairs) ⟩
        map (term ∘ proj₂) pairs
      ≡⟨ sym (tabulate-∘ (term ∘ proj₂)
            (λ i → Source.eval (Source.P steps) (children i ∷ parameters) ,
                   children i)) ⟩
        legacyChildren
      ∎

    arguments-sound :
      terms sourceArguments ≡
      (legacyResults ++ legacyChildren) ++ terms parameters
    arguments-sound =
      trans (terms-++ (map proj₁ pairs ++ map proj₂ pairs) parameters)
        (cong₂ _++_
          (trans (terms-++ (map proj₁ pairs) (map proj₂ pairs))
                 (cong₂ _++_ results-sound originals-sound))
          refl)

sound* [] xs = refl
sound* (p ∷ ps) xs = cong₂ _∷_ (sound p xs) (sound* ps xs)
