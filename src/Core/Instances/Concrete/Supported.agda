{-# OPTIONS --safe #-}

module Core.Instances.Concrete.Supported where

open import Data.Fin using (Fin; zero; suc)
import Data.Fin as Fin
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.PRFO
open import Core.Instances.Common
open import Core.Instances.Concrete.Evaluator

flatVec : ∀ {G} → (n : ℕ) → Flat G → Flat (vec G n)
flatVec zero    p = flat-𝟙
flatVec (suc n) p = flat-× p (flatVec n p)

flatBranches : ∀ {k} (rs : Vec ℕ k) → Flat (Branches rs)
flatBranches []       = flat-𝟘
flatBranches (r ∷ rs) = flat-+ (flatVec r flat-`) (flatBranches rs)

supported-lookup : ∀ {T n} (i : Fin n) → Supported (lookupᴾ {T = T} i)
supported-lookup zero    = s-π₁
supported-lookup (suc i) = s-C (supported-lookup i) s-π₂

supported-assoc : ∀ {T U V} → Supported (assoc-× {T = T} {U = U} {V = V})
supported-assoc = s-# (s-C s-π₁ s-π₁) (s-# (s-C s-π₂ s-π₁) s-π₂)

supported-mapVec : ∀ {T U} (n : ℕ) {f : T →ᴾ U} →
                   Supported f → Supported (mapVec n f)
supported-mapVec zero sf = s-id
supported-mapVec (suc n) sf =
  s-# (s-C sf s-π₁) (s-C (supported-mapVec n sf) s-π₂)

supported-appendVec : ∀ {T} (m n : ℕ) → Supported (appendVec {T = T} m n)
supported-appendVec zero n = s-π₂
supported-appendVec (suc m) n =
  s-# (s-C s-π₁ s-π₁)
      (s-C (supported-appendVec m n) (s-# (s-C s-π₂ s-π₁) s-π₂))

supported-splitPairs : ∀ {T U} (n : ℕ) → Supported (splitPairs {T = T} {U = U} n)
supported-splitPairs zero = s-# s-⊤ s-⊤
supported-splitPairs (suc n) = s-# left right
  where
  tails : Supported (C (splitPairs n) π₂)
  tails = s-C (supported-splitPairs n) s-π₂

  left : Supported (`# (C π₁ π₁) (C π₁ (C (splitPairs n) π₂)))
  left = s-# (s-C s-π₁ s-π₁) (s-C s-π₁ tails)

  right : Supported (`# (C π₂ π₁) (C π₂ (C (splitPairs n) π₂)))
  right = s-# (s-C s-π₂ s-π₁) (s-C s-π₂ tails)

supported-preparePara : ∀ {T} (r n : ℕ) → Supported (preparePara {T = T} r n)
supported-preparePara r n =
  s-C (supported-appendVec (r Data.Nat.+ r) n)
    (s-#
      (s-C (supported-appendVec r r) (s-C (supported-splitPairs r) s-π₁))
      s-π₂)

supported-injectAt : ∀ {k T} (rs : Vec ℕ k) (i : Fin k) →
                     Supported (injectAt {T = T} rs i)
supported-injectAt (r ∷ rs) Fin.zero = s-ι₁
supported-injectAt (r ∷ rs) (Fin.suc i) = s-C s-ι₂ (supported-injectAt rs i)

supported-injectBranch : ∀ {k T} (rs : Vec ℕ k) (i : Fin k) →
                         Supported (injectBranch {T = T} rs i)
supported-injectBranch {T = T} rs i rewrite branches-sub rs T = supported-injectAt rs i

supported-con : ∀ {k} (rs : Vec ℕ k) (i : Fin k) → Supported (conᴾ rs i)
supported-con rs i = s-C (s-roll (flatBranches rs)) (supported-injectBranch rs i)

supported-caseAt : ∀ {k T U V} (rs : Vec ℕ k)
  {handlers : (i : Fin k) → vec T (lookup rs i) `× U →ᴾ V} →
  ((i : Fin k) → Supported (handlers i)) → Supported (caseAt rs handlers)
supported-caseAt [] sh = s-C s-⊥ s-π₁
supported-caseAt (r ∷ rs) sh =
  s-C (s-case (sh Fin.zero) (supported-caseAt rs (λ i → sh (Fin.suc i)))) s-dist

supported-caseBranches : ∀ {k T U V} (rs : Vec ℕ k)
  {handlers : (i : Fin k) → vec T (lookup rs i) `× U →ᴾ V} →
  ((i : Fin k) → Supported (handlers i)) → Supported (caseBranches rs handlers)
supported-caseBranches {T = T} rs sh rewrite branches-sub rs T = supported-caseAt rs sh

caseAt-injectAt : ∀ {k T U V} (rs : Vec ℕ k)
  (handlers : (i : Fin k) → vec T (lookup rs i) `× U →ᴾ V)
  (sh : (i : Fin k) → Supported (handlers i))
  (i : Fin k) (x : Sem (vec T (lookup rs i))) (u : Sem U) →
  eval (supported-caseAt rs sh)
       (eval (supported-injectAt rs i) x , u) ≡
  eval (sh i) (x , u)
caseAt-injectAt (r ∷ rs) handlers sh Fin.zero x u = refl
caseAt-injectAt (r ∷ rs) handlers sh (Fin.suc i) x u =
  caseAt-injectAt rs (λ j → handlers (Fin.suc j)) (λ j → sh (Fin.suc j)) i x u

case-inject : ∀ {k T U V} (rs : Vec ℕ k)
  (handlers : (i : Fin k) → vec T (lookup rs i) `× U →ᴾ V)
  (sh : (i : Fin k) → Supported (handlers i))
  (i : Fin k) (x : Sem (vec T (lookup rs i))) (u : Sem U) →
  eval (supported-caseBranches rs sh)
       (eval (supported-injectBranch rs i) x , u) ≡
  eval (sh i) (x , u)
case-inject {T = T} rs handlers sh i x u rewrite branches-sub rs T =
  caseAt-injectAt rs handlers sh i x u

supported-paraHandler : ∀ {k n} (rs : Vec ℕ k)
  {steps : (i : Fin k) →
    vec (Tree rs) ((lookup rs i Data.Nat.+ lookup rs i) Data.Nat.+ n) →ᴾ Tree rs} →
  ((i : Fin k) → Supported (steps i)) → Supported (paraHandler rs steps)
supported-paraHandler {n = n} rs ss =
  supported-caseBranches rs λ i → s-C (ss i) (supported-preparePara (lookup rs i) n)
