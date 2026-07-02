{-# OPTIONS --safe #-}

module Core.Instances.Common where

open import Data.Bool using (_∧_)
open import Data.Fin using (Fin; zero; suc)
import Data.Fin as Fin
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

open import Core.PRFO
open import Core.Semantics.Types using (Guarded; WellFormed; Polynomial;
  poly-𝟘; poly-+; poly-ind; fo-polynomial)

----------------------------------------------------------------------
-- Object-language vectors
----------------------------------------------------------------------

vec : ∀ {n} → Ty FO n → ℕ → Ty FO n
vec T zero    = `𝟙
vec T (suc n) = T `× vec T n

lookupᴾ : ∀ {T n} → (i : Fin n) → vec T n →ᴾ T
lookupᴾ zero    = π₁
lookupᴾ (suc i) = C (lookupᴾ i) π₂

assoc-× : ∀ {T U V} → (T `× U) `× V →ᴾ T `× (U `× V)
assoc-× = `# (C π₁ π₁) (`# (C π₂ π₁) π₂)

mapVec : ∀ {T U} (n : ℕ) → (T →ᴾ U) → vec T n →ᴾ vec U n
mapVec zero    f = id
mapVec (suc n) f = map-× f (mapVec n f)

appendVec : ∀ {T} (m n : ℕ) → vec T m `× vec T n →ᴾ vec T (m + n)
appendVec zero    n = π₂
appendVec (suc m) n =
  `# (C π₁ π₁)
     (C (appendVec m n) (`# (C π₂ π₁) π₂))

splitPairs : ∀ {T U} (n : ℕ) →
             vec (T `× U) n →ᴾ vec T n `× vec U n
splitPairs zero = `# `⊤ `⊤
splitPairs (suc n) = `# left right
  where
  tails : vec (T `× U) (suc n) →ᴾ vec T n `× vec U n
  tails = C (splitPairs n) π₂

  left : vec (T `× U) (suc n) →ᴾ vec T (suc n)
  left = `# (C π₁ π₁) (C π₁ tails)

  right : vec (T `× U) (suc n) →ᴾ vec U (suc n)
  right = `# (C π₂ π₁) (C π₂ tails)

-- Turn a vector of (recursive result, original child) pairs followed by
-- parameters into the source calculi's result-vector ++ child-vector ++
-- parameter-vector convention.
preparePara : ∀ {T} (r n : ℕ) →
              vec (T `× T) r `× vec T n →ᴾ vec T ((r + r) + n)
preparePara r n =
  C (appendVec (r + r) n)
    (`# (C (appendVec r r) (C (splitPairs r) π₁)) π₂)

----------------------------------------------------------------------
-- Finite polynomial signatures
----------------------------------------------------------------------

Branches : ∀ {k} → Vec ℕ k → Ty FO 1
Branches []       = `𝟘
Branches (r ∷ rs) = vec (` Fin.zero) r `+ Branches rs

BranchesAt : ∀ {k} → Vec ℕ k → TY FO → TY FO
BranchesAt []       T = `𝟘
BranchesAt (r ∷ rs) T = vec T r `+ BranchesAt rs T

sub-vec : ∀ {n m} (r : ℕ) (T : Ty FO n) (σ : Sub FO n m) →
          sub σ (vec T r) ≡ vec (sub σ T) r
sub-vec zero    T σ = refl
sub-vec (suc r) T σ = cong₂ _`×_ refl (sub-vec r T σ)

branches-sub : ∀ {k} (rs : Vec ℕ k) (T : TY FO) →
               Branches rs [ T ] ≡ BranchesAt rs T
branches-sub []       T = refl
branches-sub (r ∷ rs) T =
  cong₂ _`+_ (sub-vec r (` Fin.zero) (σ₀ T)) (branches-sub rs T)

Tree : ∀ {k} → Vec ℕ k → TY FO
Tree rs = ind (Branches rs)

----------------------------------------------------------------------
-- Formation evidence for generated finite signatures
----------------------------------------------------------------------

Branches-guarded : ∀ {k} (rs : Vec ℕ k) → Guarded (Branches rs)
Branches-guarded [] = refl
Branches-guarded (r ∷ rs) = refl

vec-wellFormed : ∀ {n} (r : ℕ) (T : Ty FO n) →
  WellFormed T → WellFormed (vec T r)
vec-wellFormed zero T wellFormed-T = refl
vec-wellFormed (suc r) T wellFormed-T
  rewrite wellFormed-T | vec-wellFormed r T wellFormed-T = refl

Branches-wellFormed : ∀ {k} (rs : Vec ℕ k) → WellFormed (Branches rs)
Branches-wellFormed [] = refl
Branches-wellFormed (r ∷ rs) =
  cong₂ _∧_ (vec-wellFormed r (` Fin.zero) refl)
             (Branches-wellFormed rs)

Branches-polynomial : ∀ {k} (rs : Vec ℕ k) → Polynomial (Branches rs)
Branches-polynomial [] = poly-𝟘
Branches-polynomial (r ∷ rs) =
  poly-+ (fo-polynomial (vec (` Fin.zero) r)) (Branches-polynomial rs)

Tree-wellFormed : ∀ {k} (rs : Vec ℕ k) → WellFormed (Tree rs)
Tree-wellFormed rs =
  cong₂ _∧_ (Branches-guarded rs) (Branches-wellFormed rs)

Tree-polynomial : ∀ {k} (rs : Vec ℕ k) → Polynomial (Tree rs)
Tree-polynomial rs = poly-ind (Branches-polynomial rs)

-- Named from the generated fixed point's perspective: Guarded applies to its
-- open generator, while WellFormed and Polynomial apply to the closed tree.
Tree-guarded : ∀ {k} (rs : Vec ℕ k) → Guarded (Branches rs)
Tree-guarded = Branches-guarded

injectAt : ∀ {k T} (rs : Vec ℕ k) (i : Fin k) →
           vec T (lookup rs i) →ᴾ BranchesAt rs T
injectAt (r ∷ rs) Fin.zero    = ι₁
injectAt (r ∷ rs) (Fin.suc i) = C ι₂ (injectAt rs i)

injectBranch : ∀ {k T} (rs : Vec ℕ k) (i : Fin k) →
               vec T (lookup rs i) →ᴾ Branches rs [ T ]
injectBranch {T = T} rs i rewrite branches-sub rs T = injectAt rs i

conᴾ : ∀ {k} (rs : Vec ℕ k) (i : Fin k) →
       vec (Tree rs) (lookup rs i) →ᴾ Tree rs
conᴾ rs i = C roll (injectBranch rs i)

caseAt : ∀ {k T U V} (rs : Vec ℕ k) →
  ((i : Fin k) → vec T (lookup rs i) `× U →ᴾ V) →
  BranchesAt rs T `× U →ᴾ V
caseAt [] handlers = C `⊥ π₁
caseAt (r ∷ rs) handlers =
  C (`case (handlers Fin.zero) (caseAt rs (λ i → handlers (Fin.suc i))))
    dist-+-×

caseBranches : ∀ {k T U V} (rs : Vec ℕ k) →
  ((i : Fin k) → vec T (lookup rs i) `× U →ᴾ V) →
  (Branches rs [ T ]) `× U →ᴾ V
caseBranches {T = T} rs handlers rewrite branches-sub rs T = caseAt rs handlers

paraHandler : ∀ {k n} (rs : Vec ℕ k) →
  ((i : Fin k) → vec (Tree rs) ((lookup rs i + lookup rs i) + n) →ᴾ Tree rs) →
  (Branches rs [ Tree rs `× Tree rs ]) `× vec (Tree rs) n →ᴾ Tree rs
paraHandler {n = n} rs steps =
  caseBranches rs λ i → C (steps i) (preparePara (lookup rs i) n)
