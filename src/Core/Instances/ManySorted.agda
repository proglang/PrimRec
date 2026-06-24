{-# OPTIONS --safe #-}

module Core.Instances.ManySorted where

open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; _∷_)
open import Level using (Level)

open import Core.PRFO
open import Core.Instances.Common
import Core.Instances.Model as InstanceModel
import Core.Instances.Source.ManySorted as Source
import Core.Instances.Source.Trees as TreeSource
import Core.Instances.Trees as Trees
import Core.Models.PRFO as Model

-- All source sorts embed into a single tagged term algebra.  Source typing is
-- retained by Source.PR; the target intentionally erases sort indices.
Target : ∀ {S} → Source.Signature S → TY FO
Target Sig = Tree (Source.ranks Sig)

eraseContext : ∀ {S n} (Sig : Source.Signature S) → Vec S n → TY FO
eraseContext {n = n} Sig ss = vec (Target Sig) n

erase : ∀ {S n s} {Sig : Source.Signature S} {ss : Vec S n} →
  Source.PR Sig (ss , s) → TreeSource.PR (TreeSource.ranked (Source.ranks Sig)) n
erase* : ∀ {S n m} {Sig : Source.Signature S}
  {ss : Vec S n} {us : Vec S m} →
  Source.PR* Sig (ss , us) →
  Vec (TreeSource.PR (TreeSource.ranked (Source.ranks Sig)) n) m

erase (Source.σ a) = TreeSource.σ a
erase (Source.π i) = TreeSource.π i
erase (Source.C f fs) = TreeSource.C (erase f) (erase* fs)
erase (Source.P res steps) = TreeSource.P (λ a → erase (steps a))

erase* Source.[] = []
erase* (p Source.∷ ps) = erase p ∷ erase* ps

compile : ∀ {S n s} {Sig : Source.Signature S} {ss : Vec S n} →
          Source.PR Sig (ss , s) → vec (Target Sig) n →ᴾ Target Sig
compile* : ∀ {S n m} {Sig : Source.Signature S}
           {ss : Vec S n} {us : Vec S m} →
           Source.PR* Sig (ss , us) →
           vec (Target Sig) n →ᴾ vec (Target Sig) m

compile p = Trees.compile (erase p)
compile* ps = Trees.compile* (erase* ps)

compile-typed : ∀ {S n s} {Sig : Source.Signature S} {ss : Vec S n} →
                Source.PR Sig (ss , s) → Set
compile-typed {Sig = Sig} {ss = ss} p = eraseContext Sig ss →ᴾ Target Sig

typed : ∀ {S n s} {Sig : Source.Signature S} {ss : Vec S n}
        (p : Source.PR Sig (ss , s)) → compile-typed p
typed = compile

-- Sort contexts are intrinsic indices rather than substitutable type codes.
-- Their erasure is determined solely by context length.

----------------------------------------------------------------------
-- Categorical source semantics and preservation
----------------------------------------------------------------------

module Semantics {ℓ : Level} (M : Model.Model ℓ) where
  open Model.Model M
  open InstanceModel.For M

  denote : ∀ {S n s} {Sig : Source.Signature S} {ss : Vec S n} →
           Source.PR Sig (ss , s) → vec (Target Sig) n ⇒ᴹ Target Sig
  denote* : ∀ {S n m} {Sig : Source.Signature S}
            {ss : Vec S n} {us : Vec S m} →
            Source.PR* Sig (ss , us) →
            vec (Target Sig) n ⇒ᴹ vec (Target Sig) m

  denote {Sig = Sig} (Source.σ a) =
    Model.interpret structure (conᴾ (Source.ranks Sig) a)
  denote (Source.π i) = Model.interpret structure (lookupᴾ i)
  denote (Source.C f fs) = Cᴹ (denote f) (denote* fs)
  denote {n = suc n} {Sig = Sig} (Source.P res steps) =
    Pᴹ (paraHandlerᴹ (Source.ranks Sig) (λ i → denote (steps i)))

  denote* Source.[] = ⊤ᴹ
  denote* (p Source.∷ ps) = pairᴹ (denote p) (denote* ps)

  preserves : ∀ {S n s} {Sig : Source.Signature S} {ss : Vec S n}
              (p : Source.PR Sig (ss , s)) →
              Model.interpret structure (compile p) ≈ᴹ denote p
  preserves* : ∀ {S n m} {Sig : Source.Signature S}
               {ss : Vec S n} {us : Vec S m}
               (ps : Source.PR* Sig (ss , us)) →
               Model.interpret structure (compile* ps) ≈ᴹ denote* ps

  preserves (Source.σ a) = ≈-reflᴹ
  preserves (Source.π i) = ≈-reflᴹ
  preserves (Source.C f fs) = C-congᴹ (preserves f) (preserves* fs)
  preserves {n = suc n} {Sig = Sig} (Source.P res steps) =
    P-congᴹ
      (≈-transᴹ
        (paraHandler-interpret (Source.ranks Sig) (λ i → compile (steps i)))
        (paraHandler-congᴹ (Source.ranks Sig) (λ i → preserves (steps i))))

  preserves* Source.[] = ≈-reflᴹ
  preserves* (p Source.∷ ps) = pair-congᴹ (preserves p) (preserves* ps)

  infix 4 _≈Source_
  _≈Source_ : ∀ {S n s} {Sig : Source.Signature S} {ss : Vec S n} →
    Source.PR Sig (ss , s) → Source.PR Sig (ss , s) → Set ℓ
  p ≈Source q = denote p ≈ᴹ denote q

  equations-preserved : ∀ {S n s} {Sig : Source.Signature S} {ss : Vec S n}
    {p q : Source.PR Sig (ss , s)} →
    p ≈Source q →
    Model.interpret structure (compile p) ≈ᴹ Model.interpret structure (compile q)
  equations-preserved {p = p} {q = q} equation =
    ≈-transᴹ (preserves p) (≈-transᴹ equation (≈-symᴹ (preserves q)))
