{-# OPTIONS --safe #-}

module Core.Translations.PRFOToPRHO where

open import Data.Fin using (Fin; zero; suc)
import Data.Nat as Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂)

import Core.PRFO as FO
import Core.PRHO as HO
import Core.Equations.PRFO as FOEq
import Core.Equations.PRHO as HOEq
import Core.Types as Ty
open Ty using (FO; HO; Ty; TY; lift)

----------------------------------------------------------------------
-- Type-code compatibility lemmas
----------------------------------------------------------------------

sub-cong : ∀ {mode n m} {σ τ : Ty.Sub mode n m} →
  ((i : Fin n) → σ i ≡ τ i) →
  (T : Ty mode n) → Ty.sub σ T ≡ Ty.sub τ T
sub-cong pointwise Ty.`𝟘 = refl
sub-cong pointwise Ty.`𝟙 = refl
sub-cong pointwise (T Ty.`× U) =
  cong₂ Ty._`×_ (sub-cong pointwise T) (sub-cong pointwise U)
sub-cong pointwise (T Ty.`+ U) =
  cong₂ Ty._`+_ (sub-cong pointwise T) (sub-cong pointwise U)
sub-cong pointwise (T Ty.`⇒ U) =
  cong (T Ty.`⇒_) (sub-cong pointwise U)
sub-cong pointwise (Ty.` i) = pointwise i
sub-cong {σ = σ} {τ = τ} pointwise (Ty.ind G) =
  cong Ty.ind (sub-cong ext-pointwise G)
  where
  ext-pointwise : ∀ i → Ty.extˢ σ i ≡ Ty.extˢ τ i
  ext-pointwise zero = refl
  ext-pointwise (suc i) = cong (Ty.ren suc) (pointwise i)

lift-ren : ∀ {n m} (ρ : Ty.Ren n m) (T : Ty FO n) →
  lift (Ty.ren ρ T) ≡ Ty.ren ρ (lift T)
lift-ren ρ Ty.`𝟘 = refl
lift-ren ρ Ty.`𝟙 = refl
lift-ren ρ (T Ty.`× U) =
  cong₂ Ty._`×_ (lift-ren ρ T) (lift-ren ρ U)
lift-ren ρ (T Ty.`+ U) =
  cong₂ Ty._`+_ (lift-ren ρ T) (lift-ren ρ U)
lift-ren ρ (Ty.` i) = refl
lift-ren ρ (Ty.ind G) =
  cong Ty.ind (lift-ren (Ty.extᴿ ρ) G)

lift-extˢ : ∀ {n m} (σ : Ty.Sub FO n m) →
  (i : Fin (Nat.suc n)) →
  lift (Ty.extˢ σ i) ≡ Ty.extˢ (λ j → lift (σ j)) i
lift-extˢ σ zero = refl
lift-extˢ σ (suc i) = lift-ren suc (σ i)

lift-sub : ∀ {n m} (σ : Ty.Sub FO n m) (T : Ty FO n) →
  lift (Ty.sub σ T) ≡ Ty.sub (λ i → lift (σ i)) (lift T)
lift-sub σ Ty.`𝟘 = refl
lift-sub σ Ty.`𝟙 = refl
lift-sub σ (T Ty.`× U) =
  cong₂ Ty._`×_ (lift-sub σ T) (lift-sub σ U)
lift-sub σ (T Ty.`+ U) =
  cong₂ Ty._`+_ (lift-sub σ T) (lift-sub σ U)
lift-sub σ (Ty.` i) = refl
lift-sub σ (Ty.ind G) =
  cong Ty.ind
    (trans (lift-sub (Ty.extˢ σ) G)
      (sub-cong (lift-extˢ σ) (lift G)))

lift-σ₀ : (T : TY FO) → (i : Fin 1) →
  lift (Ty.σ₀ T i) ≡ Ty.σ₀ (lift T) i
lift-σ₀ T zero = refl

lift-⇐ : (G : Ty FO 1) (T : TY FO) →
  lift (G Ty.⇐ T) ≡ lift G Ty.⇐ lift T
lift-⇐ G T =
  trans (lift-sub (Ty.σ₀ T) G)
        (sub-cong (lift-σ₀ T) (lift G))

cast : ∀ {A₀ A₁ B₀ B₁ : TY HO} →
  A₀ ≡ A₁ → B₀ ≡ B₁ → A₀ HO.→ᴾ B₀ → A₁ HO.→ᴾ B₁
cast refl refl f = f

cast-cong : ∀ {A₀ A₁ B₀ B₁ : TY HO}
  (domain : A₀ ≡ A₁) (codomain : B₀ ≡ B₁)
  {f g : A₀ HO.→ᴾ B₀} →
  f HOEq.≈ g → cast domain codomain f HOEq.≈ cast domain codomain g
cast-cong refl refl equation = equation

fmap-id-cast : ∀ {A A′ : TY HO} (G : Ty HO 1)
  (pA : G Ty.⇐ A ≡ A′) →
  cast pA pA (HO.fmap G HO.id) HOEq.≈ HO.id
fmap-id-cast G refl = HOEq.fmap-id G

fmap-C-cast : ∀ {A B D GA GB GD : TY HO}
  (G : Ty HO 1)
  (pA : G Ty.⇐ A ≡ GA)
  (pB : G Ty.⇐ B ≡ GB)
  (pD : G Ty.⇐ D ≡ GD)
  {f : B HO.→ᴾ D} {g : A HO.→ᴾ B} →
  cast pA pD (HO.fmap G (HO.C f g)) HOEq.≈
  HO.C (cast pB pD (HO.fmap G f))
       (cast pA pB (HO.fmap G g))
fmap-C-cast G refl refl refl = HOEq.fmap-C G

strength-naturalˡ-cast :
  ∀ {A B D GA GB GAD GBD : TY HO}
  (G : Ty HO 1)
  (pA : G Ty.⇐ A ≡ GA)
  (pB : G Ty.⇐ B ≡ GB)
  (pAD : G Ty.⇐ (A Ty.`× D) ≡ GAD)
  (pBD : G Ty.⇐ (B Ty.`× D) ≡ GBD)
  {f : A HO.→ᴾ B} →
  HO.C
    (cast pAD pBD (HO.fmap G (HO.map-× f HO.id)))
    (cast (cong₂ Ty._`×_ pA refl) pAD (HO.strength G))
  HOEq.≈
  HO.C
    (cast (cong₂ Ty._`×_ pB refl) pBD (HO.strength G))
    (HO.map-× (cast pA pB (HO.fmap G f)) HO.id)
strength-naturalˡ-cast G refl refl refl refl =
  HOEq.strength-naturalˡ G

strength-naturalʳ-cast :
  ∀ {A B D GA GAB GAD : TY HO}
  (G : Ty HO 1)
  (pA : G Ty.⇐ A ≡ GA)
  (pAB : G Ty.⇐ (A Ty.`× B) ≡ GAB)
  (pAD : G Ty.⇐ (A Ty.`× D) ≡ GAD)
  {g : B HO.→ᴾ D} →
  HO.C
    (cast pAB pAD (HO.fmap G (HO.map-× HO.id g)))
    (cast (cong₂ Ty._`×_ pA refl) pAB (HO.strength G))
  HOEq.≈
  HO.C
    (cast (cong₂ Ty._`×_ pA refl) pAD (HO.strength G))
    (HO.map-× HO.id g)
strength-naturalʳ-cast G refl refl refl =
  HOEq.strength-naturalʳ G

strength-π₁-cast :
  ∀ {A B GA GAB : TY HO}
  (G : Ty HO 1)
  (pA : G Ty.⇐ A ≡ GA)
  (pAB : G Ty.⇐ (A Ty.`× B) ≡ GAB) →
  HO.C
    (cast pAB pA (HO.fmap G HO.π₁))
    (cast (cong₂ Ty._`×_ pA refl) pAB (HO.strength G))
  HOEq.≈ HO.π₁
strength-π₁-cast G refl refl =
  HOEq.strength-π₁ G

P-β-cast :
  ∀ {A B GI GIB GAI : TY HO}
  (G : Ty HO 1)
  (eI : GI ≡ G Ty.⇐ Ty.ind G)
  (eIB : GIB ≡ G Ty.⇐ (Ty.ind G Ty.`× B))
  (eAI : GAI ≡ G Ty.⇐ (A Ty.`× Ty.ind G))
  {h : GAI Ty.`× B HO.→ᴾ A} →
  let hᴾ = cast (cong₂ Ty._`×_ eAI refl) refl h
      p = HO.P {G = G} hᴾ in
  HO.C p (HO.map-× (cast (sym eI) refl HO.fold) HO.id)
  HOEq.≈
  HO.C h
    (HO.`#
      (HO.C
        (cast (sym eIB) (sym eAI)
          (HO.fmap G (HO.`# p HO.π₁)))
        (cast (cong₂ Ty._`×_ (sym eI) refl) (sym eIB)
          (HO.strength G)))
      HO.π₂)
P-β-cast G refl refl refl = HOEq.P-β

P-unique-cast :
  ∀ {A B GI GIB GAI : TY HO}
  (G : Ty HO 1)
  (eI : GI ≡ G Ty.⇐ Ty.ind G)
  (eIB : GIB ≡ G Ty.⇐ (Ty.ind G Ty.`× B))
  (eAI : GAI ≡ G Ty.⇐ (A Ty.`× Ty.ind G))
  {h : GAI Ty.`× B HO.→ᴾ A}
  {p : Ty.ind G Ty.`× B HO.→ᴾ A} →
  let hᴾ = cast (cong₂ Ty._`×_ eAI refl) refl h in
  HO.C p (HO.map-× (cast (sym eI) refl HO.fold) HO.id)
  HOEq.≈
  HO.C h
    (HO.`#
      (HO.C
        (cast (sym eIB) (sym eAI)
          (HO.fmap G (HO.`# p HO.π₁)))
        (cast (cong₂ Ty._`×_ (sym eI) refl) (sym eIB)
          (HO.strength G)))
      HO.π₂)
  →
  p HOEq.≈ HO.P {G = G} hᴾ
P-unique-cast G refl refl refl premise = HOEq.P-unique premise

----------------------------------------------------------------------
-- Structural embedding of PR-FO into PR-HO
----------------------------------------------------------------------

translate : ∀ {T U} → T FO.→ᴾ U → lift T HO.→ᴾ lift U
translate FO.id = HO.id
translate (FO.C f g) = HO.C (translate f) (translate g)
translate FO.`⊤ = HO.`⊤
translate FO.`⊥ = HO.`⊥
translate (FO.`# f g) = HO.`# (translate f) (translate g)
translate FO.π₁ = HO.π₁
translate FO.π₂ = HO.π₂
translate FO.ι₁ = HO.ι₁
translate FO.ι₂ = HO.ι₂
translate (FO.`case f g) = HO.`case (translate f) (translate g)
translate FO.dist-+-× = HO.dist-+-×
translate (FO.fmap {T = T} {U = U} G f) =
  cast (sym (lift-⇐ G T)) (sym (lift-⇐ G U))
    (HO.fmap (lift G) (translate f))
translate (FO.strength {T = T} {U = U} G) =
  cast
    (cong₂ Ty._`×_ (sym (lift-⇐ G T)) refl)
    (sym (lift-⇐ G (T Ty.`× U)))
    (HO.strength (lift G))
translate (FO.fold {G = G}) =
  cast (sym (lift-⇐ G (Ty.ind G))) refl HO.fold
translate {T = Ty.ind G Ty.`× U} {U = T} (FO.P h) =
  HO.P
    (cast
      (cong₂ Ty._`×_ (lift-⇐ G (T Ty.`× Ty.ind G)) refl)
      refl
      (translate h))

----------------------------------------------------------------------
-- Equation preservation
----------------------------------------------------------------------

preserves : ∀ {T U} {f g : T FO.→ᴾ U} →
  f FOEq.≈ g → translate f HOEq.≈ translate g
preserves FOEq.≈-refl = HOEq.≈-refl
preserves (FOEq.≈-sym p) = HOEq.≈-sym (preserves p)
preserves (FOEq.≈-trans p q) =
  HOEq.≈-trans (preserves p) (preserves q)
preserves (FOEq.C-cong p q) =
  HOEq.C-cong (preserves p) (preserves q)
preserves (FOEq.`#-cong p q) =
  HOEq.`#-cong (preserves p) (preserves q)
preserves (FOEq.`case-cong p q) =
  HOEq.`case-cong (preserves p) (preserves q)
preserves (FOEq.fmap-cong {A = A} {B = B} G p) =
  cast-cong (sym (lift-⇐ G A)) (sym (lift-⇐ G B))
    (HOEq.fmap-cong (lift G) (preserves p))
preserves (FOEq.P-cong {A = A} {B = B} {H = H} p) =
  HOEq.P-cong
    (cast-cong
      (cong₂ Ty._`×_ (lift-⇐ H (A Ty.`× Ty.ind H)) refl)
      refl
      (preserves p))
preserves FOEq.C-idˡ = HOEq.C-idˡ
preserves FOEq.C-idʳ = HOEq.C-idʳ
preserves FOEq.C-assoc = HOEq.C-assoc
preserves (FOEq.fmap-id {A = A} G) =
  fmap-id-cast (lift G) (sym (lift-⇐ G A))
preserves (FOEq.fmap-C {A = A} {B = B} {D = D} G) =
  fmap-C-cast (lift G)
    (sym (lift-⇐ G A)) (sym (lift-⇐ G B)) (sym (lift-⇐ G D))
preserves (FOEq.strength-naturalˡ {A = A} {B = B} {D = D} G) =
  strength-naturalˡ-cast (lift G)
    (sym (lift-⇐ G A))
    (sym (lift-⇐ G B))
    (sym (lift-⇐ G (A Ty.`× D)))
    (sym (lift-⇐ G (B Ty.`× D)))
preserves (FOEq.strength-naturalʳ {A = A} {B = B} {D = D} G) =
  strength-naturalʳ-cast (lift G)
    (sym (lift-⇐ G A))
    (sym (lift-⇐ G (A Ty.`× B)))
    (sym (lift-⇐ G (A Ty.`× D)))
preserves (FOEq.strength-π₁ {A = A} {B = B} G) =
  strength-π₁-cast (lift G)
    (sym (lift-⇐ G A))
    (sym (lift-⇐ G (A Ty.`× B)))
preserves FOEq.𝟙-unique = HOEq.𝟙-unique
preserves FOEq.𝟘-unique = HOEq.𝟘-unique
preserves FOEq.×-β₁ = HOEq.×-β₁
preserves FOEq.×-β₂ = HOEq.×-β₂
preserves FOEq.×-η = HOEq.×-η
preserves FOEq.+-β₁ = HOEq.+-β₁
preserves FOEq.+-β₂ = HOEq.+-β₂
preserves FOEq.+-η = HOEq.+-η
preserves FOEq.dist-undist = HOEq.dist-undist
preserves FOEq.undist-dist = HOEq.undist-dist
preserves (FOEq.P-β {A = A} {B = B} {H = H} {h = h}) =
  P-β-cast (lift H)
    (lift-⇐ H (Ty.ind H))
    (lift-⇐ H (Ty.ind H Ty.`× B))
    (lift-⇐ H (A Ty.`× Ty.ind H))
    {h = translate h}
preserves (FOEq.P-unique {A = A} {B = B} {H = H} {h = h} p) =
  P-unique-cast (lift H)
    (lift-⇐ H (Ty.ind H))
    (lift-⇐ H (Ty.ind H Ty.`× B))
    (lift-⇐ H (A Ty.`× Ty.ind H))
    {h = translate h}
    (preserves p)
