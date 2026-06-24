{-# OPTIONS --safe #-}

module Core.Instances.Model where

open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Nat using (ℕ; _+_)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Level using (Level)

open import Core.PRFO
open import Core.Instances.Common
import Core.Models.PRFO as CModel

module For {ℓ : Level} (M : CModel.Model ℓ) where
  open CModel.Model M

  prepareParaᴹ : ∀ {T} (r n : ℕ) →
                 vec (T `× T) r `× vec T n ⇒ᴹ vec T ((r + r) + n)
  prepareParaᴹ r n = CModel.interpret structure (preparePara r n)

  caseAtᴹ : ∀ {k T U V} (rs : Vec ℕ k) →
    ((i : Fin k) → vec T (lookup rs i) `× U ⇒ᴹ V) →
    BranchesAt rs T `× U ⇒ᴹ V
  caseAtᴹ [] handlers = Cᴹ ⊥ᴹ π₁ᴹ
  caseAtᴹ (r ∷ rs) handlers =
    Cᴹ (caseᴹ (handlers Fin.zero)
              (caseAtᴹ rs (λ i → handlers (Fin.suc i))))
       distᴹ

  caseBranchesᴹ : ∀ {k T U V} (rs : Vec ℕ k) →
    ((i : Fin k) → vec T (lookup rs i) `× U ⇒ᴹ V) →
    (Branches rs ⇐ T) `× U ⇒ᴹ V
  caseBranchesᴹ {T = T} rs handlers rewrite branches-sub rs T =
    caseAtᴹ rs handlers

  paraHandlerᴹ : ∀ {k n} (rs : Vec ℕ k) →
    ((i : Fin k) → vec (Tree rs) ((lookup rs i + lookup rs i) + n) ⇒ᴹ Tree rs) →
    (Branches rs ⇐ (Tree rs `× Tree rs)) `× vec (Tree rs) n ⇒ᴹ Tree rs
  paraHandlerᴹ {n = n} rs steps =
    caseBranchesᴹ rs λ i → Cᴹ (steps i) (prepareParaᴹ (lookup rs i) n)

  caseAt-congᴹ : ∀ {k T U V} (rs : Vec ℕ k)
    {hs ks : (i : Fin k) → vec T (lookup rs i) `× U ⇒ᴹ V} →
    ((i : Fin k) → hs i ≈ᴹ ks i) →
    caseAtᴹ rs hs ≈ᴹ caseAtᴹ rs ks
  caseAt-congᴹ [] pointwise = ≈-reflᴹ
  caseAt-congᴹ (r ∷ rs) pointwise =
    C-congᴹ
      (case-congᴹ (pointwise Fin.zero)
        (caseAt-congᴹ rs (λ i → pointwise (Fin.suc i))))
      ≈-reflᴹ

  caseBranches-congᴹ : ∀ {k T U V} (rs : Vec ℕ k)
    {hs ks : (i : Fin k) → vec T (lookup rs i) `× U ⇒ᴹ V} →
    ((i : Fin k) → hs i ≈ᴹ ks i) →
    caseBranchesᴹ rs hs ≈ᴹ caseBranchesᴹ rs ks
  caseBranches-congᴹ {T = T} rs pointwise rewrite branches-sub rs T =
    caseAt-congᴹ rs pointwise

  caseAt-interpret : ∀ {k T U V} (rs : Vec ℕ k)
    (handlers : (i : Fin k) → vec T (lookup rs i) `× U →ᴾ V) →
    CModel.interpret structure (caseAt rs handlers) ≈ᴹ
      caseAtᴹ rs (λ i → CModel.interpret structure (handlers i))
  caseAt-interpret [] handlers = ≈-reflᴹ
  caseAt-interpret (r ∷ rs) handlers =
    C-congᴹ
      (case-congᴹ ≈-reflᴹ
        (caseAt-interpret rs (λ i → handlers (Fin.suc i))))
      ≈-reflᴹ

  caseBranches-interpret : ∀ {k T U V} (rs : Vec ℕ k)
    (handlers : (i : Fin k) → vec T (lookup rs i) `× U →ᴾ V) →
    CModel.interpret structure (caseBranches rs handlers) ≈ᴹ
      caseBranchesᴹ rs (λ i → CModel.interpret structure (handlers i))
  caseBranches-interpret {T = T} rs handlers rewrite branches-sub rs T =
    caseAt-interpret rs handlers

  paraHandler-congᴹ : ∀ {k n} (rs : Vec ℕ k)
    {hs ks : (i : Fin k) →
      vec (Tree rs) ((lookup rs i + lookup rs i) + n) ⇒ᴹ Tree rs} →
    ((i : Fin k) → hs i ≈ᴹ ks i) →
    paraHandlerᴹ rs hs ≈ᴹ paraHandlerᴹ rs ks
  paraHandler-congᴹ {n = n} rs pointwise =
    caseBranches-congᴹ rs λ i → C-congᴹ (pointwise i) ≈-reflᴹ

  paraHandler-interpret : ∀ {k n} (rs : Vec ℕ k)
    (steps : (i : Fin k) →
      vec (Tree rs) ((lookup rs i + lookup rs i) + n) →ᴾ Tree rs) →
    CModel.interpret structure (paraHandler rs steps) ≈ᴹ
      paraHandlerᴹ rs (λ i → CModel.interpret structure (steps i))
  paraHandler-interpret {n = n} rs steps =
    caseBranches-interpret rs
      (λ i → C (steps i) (preparePara (lookup rs i) n))
