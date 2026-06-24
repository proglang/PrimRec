{-# OPTIONS --safe #-}

module Core.Instances.Equations.Common where

open import Data.Fin using (Fin; zero; suc)
import Data.Fin as Fin
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_; lookup)

open import Core.Equations.PRFO
open import Core.Instances.Common

map-×-cong : ∀ {A B C D : TY FO}
  {f f′ : A →ᴾ C} {g g′ : B →ᴾ D} →
  f ≈ f′ → g ≈ g′ → map-× f g ≈ map-× f′ g′
map-×-cong f≈f′ g≈g′ =
  `#-cong (C-cong f≈f′ ≈-refl) (C-cong g≈g′ ≈-refl)

mapVec-cong : ∀ {T U} (n : ℕ) {f g : T →ᴾ U} →
  f ≈ g → mapVec n f ≈ mapVec n g
mapVec-cong Data.Nat.zero equation = ≈-refl
mapVec-cong (Data.Nat.suc n) equation =
  map-×-cong equation (mapVec-cong n equation)

caseAt-cong : ∀ {k T U V} (rs : Vec ℕ k)
  {hs ks : (i : Fin k) → vec T (lookup rs i) `× U →ᴾ V} →
  ((i : Fin k) → hs i ≈ ks i) →
  caseAt rs hs ≈ caseAt rs ks
caseAt-cong [] pointwise = C-cong ≈-refl ≈-refl
caseAt-cong (r ∷ rs) pointwise =
  C-cong
    (`case-cong (pointwise Fin.zero)
      (caseAt-cong rs (λ i → pointwise (Fin.suc i))))
    ≈-refl

caseBranches-cong : ∀ {k T U V} (rs : Vec ℕ k)
  {hs ks : (i : Fin k) → vec T (lookup rs i) `× U →ᴾ V} →
  ((i : Fin k) → hs i ≈ ks i) →
  caseBranches rs hs ≈ caseBranches rs ks
caseBranches-cong {T = T} rs pointwise rewrite branches-sub rs T =
  caseAt-cong rs pointwise

paraHandler-cong : ∀ {k n} (rs : Vec ℕ k)
  {hs ks : (i : Fin k) →
    vec (Tree rs) ((lookup rs i Data.Nat.+ lookup rs i) Data.Nat.+ n)
      →ᴾ Tree rs} →
  ((i : Fin k) → hs i ≈ ks i) →
  paraHandler rs hs ≈ paraHandler rs ks
paraHandler-cong {n = n} rs pointwise =
  caseBranches-cong rs λ i →
    C-cong (pointwise i) ≈-refl
