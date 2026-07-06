module Core.Instances.Legacy.PRHTrees where

-- Compatibility with the original heterogeneous-tree development.  As with
-- the PR-Trees bridge, this module cannot be part of the --safe Core aggregate
-- because PR-HTrees marks its evaluator TERMINATING.  The two local
-- TERMINATING annotations below cover structurally recursive traversals through
-- function-valued child collections, which Agda's checker does not recognize;
-- no postulates are introduced.

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; _∷_; lookup; map; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; cong₂)
open Eq.≡-Reasoning

import PR-HTrees as Legacy
import PR-Trees as LegacyTrees
import Core.Instances.Source.ManySorted as Source
open import Core.Instances.Legacy.Finite
import Core.Instances.Legacy.PRTrees as TreesBridge
open import Core.PRFO using (_→ᴾ_)
open import Core.Instances.Common using (vec)
import Core.Instances.Trees as CoreTrees

------------------------------------------------------------------------
-- Signatures, terms, environments, and programs
------------------------------------------------------------------------

signature : ∀ {S} → Source.Signature S → Legacy.Sorted S
signature Sig =
  Legacy.mkSorted
    (λ a → lookup (Source.ranks Sig) a)
    (Source.inputs Sig)
    (Source.output Sig)

-- PR-HTrees also leaves the constructor set unconstrained.  Sorts may remain
-- arbitrary; Core only needs a finite presentation of the constructors.
record FiniteSignature {S : Set} (Sig : Legacy.Sorted S) : Set where
  constructor finiteSignature
  field
    symbols-finite : Finite (Legacy.symbols Sig)

open FiniteSignature public

sourceSignature : ∀ {S} (Sig : Legacy.Sorted S) →
  FiniteSignature Sig → Source.Signature S
sourceSignature {S} Sig finiteSig = Source.signature ranks inputs output
  where
  presentation = symbols-finite finiteSig

  ranks = tabulate (λ i → Legacy.rank Sig (decode presentation i))

  rank-decode : ∀ i → lookup ranks i ≡ Legacy.rank Sig (decode presentation i)
  rank-decode i = lookup∘tabulate _ i

  inputs : ∀ i → Vec _ (lookup ranks i)
  inputs i = Eq.subst (Vec _) (Eq.sym (rank-decode i))
    (Legacy.sin* Sig (decode presentation i))

  output : Fin (size presentation) → S
  output i = Legacy.sout Sig (decode presentation i)

signature-finite : ∀ {S} (Sig : Source.Signature S) →
  FiniteSignature (signature Sig)
signature-finite Sig = finiteSignature (finiteFin (Source.count Sig))

-- Erase intrinsic sorts while retaining the legacy ranked-tree program.  This
-- factors the reverse bridge through the finite PR-Trees bridge and matches
-- the sort erasure used by Core.Instances.ManySorted.
ranked : ∀ {S} → Legacy.Sorted S → LegacyTrees.Ranked
ranked Sig = LegacyTrees.mkRanked (Legacy.rank Sig)

eraseProgram : ∀ {S n s} {Sig : Legacy.Sorted S} {ss : Vec S n} →
  Legacy.PR Sig (ss , s) → LegacyTrees.PR (ranked Sig) n
erasePrograms : ∀ {S n m} {Sig : Legacy.Sorted S}
  {ss : Vec S n} {us : Vec S m} →
  Legacy.PR* Sig (ss , us) → Vec (LegacyTrees.PR (ranked Sig) n) m

eraseProgram (Legacy.σ a) = LegacyTrees.σ a
eraseProgram (Legacy.π i) = LegacyTrees.π i
eraseProgram (Legacy.C f fs) =
  LegacyTrees.C (eraseProgram f) (erasePrograms fs)
eraseProgram (Legacy.Pr res steps) =
  LegacyTrees.Pr (λ a → eraseProgram (steps a))

erasePrograms Legacy.[] = []
erasePrograms (p Legacy.∷ ps) = eraseProgram p ∷ erasePrograms ps

ranked-finite : ∀ {S} {Sig : Legacy.Sorted S} →
  FiniteSignature Sig → TreesBridge.FiniteSignature (ranked Sig)
ranked-finite finiteSig =
  TreesBridge.finiteSignature (symbols-finite finiteSig)

compileLegacy : ∀ {S n s} {Sig : Legacy.Sorted S} {ss : Vec S n}
  (finiteSig : FiniteSignature Sig) → Legacy.PR Sig (ss , s) →
  vec (CoreTrees.Target
    (TreesBridge.sourceSignature (ranked Sig) (ranked-finite finiteSig))) n →ᴾ
  CoreTrees.Target
    (TreesBridge.sourceSignature (ranked Sig) (ranked-finite finiteSig))
compileLegacy finiteSig p =
  TreesBridge.compileLegacy (ranked-finite finiteSig) (eraseProgram p)

mutual
  {-# TERMINATING #-}
  term : ∀ {S s} {Sig : Source.Signature S} →
    Source.Term Sig s → Legacy.Term (signature Sig) s
  term {Sig = Sig} (Source.con a children) =
    Legacy.con a (children* (Source.inputs Sig a) children)

  children* : ∀ {S n} {Sig : Source.Signature S} (ss : Vec S n) →
    ((i : Fin n) → Source.Term Sig (lookup ss i)) →
    Legacy.Term* (signature Sig) ss
  children* [] children = Legacy.[]
  children* (s ∷ ss) children =
    term (children zero) Legacy.∷ children* ss (λ i → children (suc i))

environment : ∀ {S n} {Sig : Source.Signature S} {ss : Vec S n} →
  Source.Env Sig ss → Legacy.Term* (signature Sig) ss
environment Source.[] = Legacy.[]
environment (x Source.∷ xs) = term x Legacy.∷ environment xs

program : ∀ {S n s} {Sig : Source.Signature S} {ss : Vec S n} →
  Source.PR Sig (ss , s) → Legacy.PR (signature Sig) (ss , s)
programs : ∀ {S n m} {Sig : Source.Signature S}
  {ss : Vec S n} {us : Vec S m} →
  Source.PR* Sig (ss , us) → Legacy.PR* (signature Sig) (ss , us)

program (Source.σ a) = Legacy.σ a
program (Source.π i) = Legacy.π i
program (Source.C f fs) = Legacy.C (program f) (programs fs)
program (Source.Pr res steps) = Legacy.Pr res (λ a → program (steps a))

programs Source.[] = Legacy.[]
programs (p Source.∷ ps) = program p Legacy.∷ programs ps

------------------------------------------------------------------------
-- Structural compatibility lemmas
------------------------------------------------------------------------

environment-append : ∀ {S m n} {Sig : Source.Signature S}
  {ss : Vec S m} {us : Vec S n}
  (xs : Source.Env Sig ss) (ys : Source.Env Sig us) →
  environment (Source.appendEnv xs ys) ≡
  environment xs Legacy.++ᴬ environment ys
environment-append Source.[] ys = refl
environment-append (x Source.∷ xs) ys =
  cong (term x Legacy.∷_) (environment-append xs ys)

children-environment-lookup : ∀ {S n} {Sig : Source.Signature S}
  {ss : Vec S n} (xs : Source.Env Sig ss) →
  children* ss (Source.lookupEnv xs) ≡ environment xs
children-environment-lookup Source.[] = refl
children-environment-lookup (x Source.∷ xs) =
  cong (term x Legacy.∷_) (children-environment-lookup xs)

term-lookup : ∀ {S n} {Sig : Source.Signature S}
  {ss : Vec S n} (xs : Source.Env Sig ss) (i : Fin n) →
  term (Source.lookupEnv xs i) ≡ Legacy.alookup (environment xs) i
term-lookup (x Source.∷ xs) zero = refl
term-lookup (x Source.∷ xs) (suc i) = term-lookup xs i

environment-tabulate : ∀ {S n} {Sig : Source.Signature S}
  (ss : Vec S n)
  (children : (i : Fin n) → Source.Term Sig (lookup ss i)) →
  environment (Source.tabulateEnv children) ≡
  children* ss children
environment-tabulate [] children = refl
environment-tabulate (s ∷ ss) children =
  cong (term (children zero) Legacy.∷_)
    (environment-tabulate ss (λ i → children (suc i)))

------------------------------------------------------------------------
-- The legacy and Core-source evaluators commute
------------------------------------------------------------------------

{-# TERMINATING #-}
sound : ∀ {S n s} {Sig : Source.Signature S} {ss : Vec S n}
  (p : Source.PR Sig (ss , s)) (xs : Source.Env Sig ss) →
  term (Source.eval p xs) ≡ Legacy.eval (program p) (environment xs)
sound* : ∀ {S n m} {Sig : Source.Signature S}
  {ss : Vec S n} {us : Vec S m}
  (ps : Source.PR* Sig (ss , us)) (xs : Source.Env Sig ss) →
  environment (Source.eval* ps xs) ≡
  Legacy.eval* (programs ps) (environment xs)

sound (Source.σ a) xs = cong (Legacy.con a) (children-environment-lookup xs)
sound (Source.π i) xs = term-lookup xs i
sound (Source.C f fs) xs =
  trans (sound f (Source.eval* fs xs))
        (cong (Legacy.eval (program f)) (sound* fs xs))
sound {n = suc n} {Sig = Sig} {ss = s₀ ∷ ss} (Source.Pr res steps)
  (tree Source.∷ parameters) = go tree
  where
  legacyP : ∀ {s} →
    Legacy.PR (signature Sig) (s ∷ ss , res s)
  legacyP = Legacy.Pr res (λ a → program (steps a))

  go : ∀ {s₀} (tree : Source.Term Sig s₀) →
    term (Source.eval (Source.Pr res steps) (tree Source.∷ parameters)) ≡
    Legacy.eval legacyP (term tree Legacy.∷ environment parameters)
  go (Source.con a children) =
    begin
      term (Source.eval (Source.Pr res steps)
        (Source.con a children Source.∷ parameters))
    ≡⟨ cong term (Source.eval-Pr-con res steps a children parameters) ⟩
      term (Source.eval (steps a) sourceArguments)
    ≡⟨ sound (steps a) sourceArguments ⟩
      Legacy.eval (program (steps a)) (environment sourceArguments)
    ≡⟨ cong (Legacy.eval (program (steps a))) arguments-sound ⟩
      Legacy.eval legacyP
        (term (Source.con a children) Legacy.∷ environment parameters)
    ∎
    where
    inputSorts = Source.inputs Sig a

    sourceResults = Source.tabulateMapEnv res inputSorts
      (λ i → Source.eval (Source.Pr res steps)
        (children i Source.∷ parameters))
    sourceOriginals = Source.tabulateEnv children
    sourceArguments = Source.appendEnv
      (Source.appendEnv sourceResults sourceOriginals) parameters

    legacyChildren = children* inputSorts children
    legacyResults = Legacy.mapᴬ
      (λ _ child → Legacy.eval legacyP
        (child Legacy.∷ environment parameters))
      legacyChildren

    results-sound : environment sourceResults ≡ legacyResults
    results-sound = results inputSorts children
      where
      results : ∀ {k} (ss : Vec _ k)
        (cs : (i : Fin k) → Source.Term Sig (lookup ss i)) →
        environment
          (Source.tabulateMapEnv res ss
            (λ i → Source.eval (Source.Pr res steps)
              (cs i Source.∷ parameters))) ≡
        Legacy.mapᴬ
          (λ _ child → Legacy.eval legacyP
            (child Legacy.∷ environment parameters))
          (children* ss cs)
      results [] cs = refl
      results (s ∷ ss) cs =
        cong₂ Legacy._∷_ (go (cs zero))
          (results ss (λ i → cs (suc i)))

    originals-sound : environment sourceOriginals ≡ legacyChildren
    originals-sound = environment-tabulate inputSorts children

    arguments-sound : environment sourceArguments ≡
      (legacyResults Legacy.++ᴬ legacyChildren) Legacy.++ᴬ
      environment parameters
    arguments-sound =
      trans (environment-append
              (Source.appendEnv sourceResults sourceOriginals) parameters)
        (cong (Legacy._++ᴬ environment parameters)
          (trans (environment-append sourceResults sourceOriginals)
                 (cong₂ Legacy._++ᴬ_ results-sound originals-sound)))

sound* Source.[] xs = refl
sound* (p Source.∷ ps) xs =
  cong₂ Legacy._∷_ (sound p xs) (sound* ps xs)
