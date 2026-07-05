{-# OPTIONS --safe #-}

module Core.Instances.Equations.PREC where

open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Nat using (zero; suc)
open import Data.Vec using (Vec; []; _∷_; map)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl)

import PR-Nat as Source
open import Utils using (∘-map)
open import Core.PRFO
import Core.Equations.PRFO as EqFO
open import Core.Instances.Common using (lookupᴾ)
open import Core.Instances.Nat using (compile; compile*)
open import Core.Instances.PREC
import Core.Instances.Equations.Target as TargetEq

----------------------------------------------------------------------
-- Extensional category laws for PREC
----------------------------------------------------------------------

≈ᵖʳ-refl : ∀ {n m} {fs : Hom n m} → fs ≈ᵖʳ fs
≈ᵖʳ-refl xs = refl

≈ᵖʳ-sym : ∀ {n m} {fs gs : Hom n m} → fs ≈ᵖʳ gs → gs ≈ᵖʳ fs
≈ᵖʳ-sym p xs = Eq.sym (p xs)

≈ᵖʳ-trans : ∀ {n m} {fs gs hs : Hom n m} →
  fs ≈ᵖʳ gs → gs ≈ᵖʳ hs → fs ≈ᵖʳ hs
≈ᵖʳ-trans p q xs = Eq.trans (p xs) (q xs)

eval-idᵖʳ : ∀ {n} xs → Source.eval* (idᵖʳ {n}) xs Eq.≡ xs
eval-idᵖʳ {n} xs
  rewrite Source.eval*-projections (Source.allFin n) xs
        | Source.lookup-allFin xs = refl

eval-composeᵖʳ : ∀ {n m k} (fs : Hom m k) (gs : Hom n m) xs →
  Source.eval* (fs ∘ᵖʳ gs) xs Eq.≡
  Source.eval* fs (Source.eval* gs xs)
eval-composeᵖʳ [] gs xs = refl
eval-composeᵖʳ (f ∷ fs) gs xs rewrite eval-composeᵖʳ fs gs xs = refl

id-leftᵖʳ : ∀ {n m} (fs : Hom n m) → idᵖʳ ∘ᵖʳ fs ≈ᵖʳ fs
id-leftᵖʳ fs xs
  rewrite eval-composeᵖʳ idᵖʳ fs xs
        | eval-idᵖʳ (Source.eval* fs xs) = refl

id-rightᵖʳ : ∀ {n m} (fs : Hom n m) → fs ∘ᵖʳ idᵖʳ ≈ᵖʳ fs
id-rightᵖʳ fs xs
  rewrite eval-composeᵖʳ fs idᵖʳ xs
        | eval-idᵖʳ xs = refl

assocᵖʳ : ∀ {n m k l} (hs : Hom k l) (gs : Hom m k) (fs : Hom n m) →
  hs ∘ᵖʳ (gs ∘ᵖʳ fs) ≈ᵖʳ (hs ∘ᵖʳ gs) ∘ᵖʳ fs
assocᵖʳ hs gs fs xs
  rewrite eval-composeᵖʳ hs (gs ∘ᵖʳ fs) xs
        | eval-composeᵖʳ gs fs xs
        | eval-composeᵖʳ (hs ∘ᵖʳ gs) fs xs
        | eval-composeᵖʳ hs gs (Source.eval* fs xs) = refl

----------------------------------------------------------------------
-- Category laws for the finite-Nat subcategory of PR-FO
----------------------------------------------------------------------

id-leftᴺ : ∀ {n m} {f : NatHom n m} → idᴺ ∘ᴺ f ≈ᴺ f
id-leftᴺ = EqFO.C-idˡ

id-rightᴺ : ∀ {n m} {f : NatHom n m} → f ∘ᴺ idᴺ ≈ᴺ f
id-rightᴺ = EqFO.C-idʳ

assocᴺ : ∀ {n m k l}
  {h : NatHom k l} {g : NatHom m k} {f : NatHom n m} →
  h ∘ᴺ (g ∘ᴺ f) ≈ᴺ (h ∘ᴺ g) ∘ᴺ f
assocᴺ = EqFO.C-assoc

----------------------------------------------------------------------
-- Functor laws for the Nat-instance compiler
----------------------------------------------------------------------

pair-compose :
  ∀ {A B D E : TY FO} (f : B →ᴾ D) (h : B →ᴾ E) (g : A →ᴾ B) →
  `# (C f g) (C h g) EqFO.≈ C (`# f h) g
pair-compose f h g =
  EqFO.≈-trans
    (EqFO.`#-cong (EqFO.≈-sym π₁-target) (EqFO.≈-sym π₂-target))
    EqFO.×-η
  where
  target = C (`# f h) g

  π₁-target : C π₁ target EqFO.≈ C f g
  π₁-target =
    EqFO.≈-trans EqFO.C-assoc
      (EqFO.C-cong EqFO.×-β₁ EqFO.≈-refl)

  π₂-target : C π₂ target EqFO.≈ C h g
  π₂-target =
    EqFO.≈-trans EqFO.C-assoc
      (EqFO.C-cong EqFO.×-β₂ EqFO.≈-refl)

tuple-compose :
  ∀ {A B T : TY FO} {m} (fs : Vec (B →ᴾ T) m) (g : A →ᴾ B) →
  TargetEq.tupleᴾ (map (λ f → C f g) fs) EqFO.≈
  C (TargetEq.tupleᴾ fs) g
tuple-compose [] g = EqFO.≈-sym EqFO.𝟙-unique
tuple-compose (f ∷ fs) g =
  EqFO.≈-trans
    (EqFO.`#-cong EqFO.≈-refl (tuple-compose fs g))
    (pair-compose f (TargetEq.tupleᴾ fs) g)

compile-shift-projections :
  ∀ {n m} (is : Vec (Fin n) m) →
  compile* (map (λ i → Source.π (Fin.suc i)) is) EqFO.≈
  C (compile* (map Source.π is)) π₂
compile-shift-projections [] = EqFO.≈-sym EqFO.𝟙-unique
compile-shift-projections (i ∷ is) =
  EqFO.≈-trans
    (EqFO.`#-cong EqFO.≈-refl (compile-shift-projections is))
    (pair-compose (lookupᴾ i) (compile* (map Source.π is)) π₂)

pair-idᴺ : ∀ {A B : TY FO} → `# (π₁ {U = A} {V = B}) π₂ EqFO.≈ id
pair-idᴺ =
  EqFO.≈-trans
    (EqFO.`#-cong (EqFO.≈-sym EqFO.C-idʳ)
                  (EqFO.≈-sym EqFO.C-idʳ))
    EqFO.×-η

F-id : ∀ {n} → F₁ (idᵖʳ {n}) ≈ᴺ idᴺ
F-id {zero} = EqFO.≈-sym EqFO.𝟙-unique
F-id {suc n} rewrite ∘-map Source.π Fin.suc (Source.allFin n) =
  EqFO.≈-trans
    (EqFO.`#-cong EqFO.≈-refl
      (EqFO.≈-trans
        (compile-shift-projections (Source.allFin n))
        (EqFO.C-cong (F-id {n}) EqFO.≈-refl)))
    (EqFO.≈-trans
      (EqFO.`#-cong EqFO.≈-refl EqFO.C-idˡ)
      pair-idᴺ)

F-∘ : ∀ {n m k} (fs : Hom m k) (gs : Hom n m) →
  F₁ (fs ∘ᵖʳ gs) ≈ᴺ F₁ fs ∘ᴺ F₁ gs
F-∘ [] gs = EqFO.≈-sym EqFO.𝟙-unique
F-∘ (f ∷ fs) gs =
  EqFO.≈-trans
    (EqFO.`#-cong EqFO.≈-refl (F-∘ fs gs))
    (pair-compose (compile f) (compile* fs) (compile* gs))
