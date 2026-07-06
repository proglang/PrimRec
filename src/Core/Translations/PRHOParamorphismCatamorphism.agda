{-# OPTIONS --safe #-}

module Core.Translations.PRHOParamorphismCatamorphism where

import Core.PRHO as Pr
import Core.PRHOCatamorphism as Ct
import Core.Equations.PRHO as PEq
import Core.Equations.PRHOCatamorphism as CtEq
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Types

variable
  W : TY HO

----------------------------------------------------------------------
-- Derived eliminators
----------------------------------------------------------------------

dropSubtermᴾ : ∀ {T U} (G : Ty HO 1) →
  (G [ T ]) Pr.`× U Pr.→ᴾ T →
  (G [ T Pr.`× Pr.ind G ]) Pr.`× U Pr.→ᴾ T
dropSubtermᴾ G h =
  Pr.C h (Pr.`# (Pr.C (Pr.fmap G Pr.π₁) Pr.π₁) Pr.π₂)

Ctᴾʳ : ∀ {T U} {G : Ty HO 1} →
  (G [ T ]) Pr.`× U Pr.→ᴾ T →
  Pr.ind G Pr.`× U Pr.→ᴾ T
Ctᴾʳ {G = G} h = Pr.Pr (dropSubtermᴾ G h)

rebuildᶜ : ∀ {T U} (G : Ty HO 1) →
  (G [ T Ct.`× Ct.ind G ]) Ct.`× U Ct.→ᶜ Ct.ind G
rebuildᶜ G =
  Ct.C Ct.con (Ct.C (Ct.fmap G Ct.π₂) Ct.π₁)

rememberᶜ : ∀ {T U} (G : Ty HO 1) →
  (G [ T Ct.`× Ct.ind G ]) Ct.`× U Ct.→ᶜ T →
  (G [ T Ct.`× Ct.ind G ]) Ct.`× U Ct.→ᶜ T Ct.`× Ct.ind G
rememberᶜ G h = Ct.`# h (rebuildᶜ G)

Prᶜ : ∀ {T U} {G : Ty HO 1} →
  (G [ T Ct.`× Ct.ind G ]) Ct.`× U Ct.→ᶜ T →
  Ct.ind G Ct.`× U Ct.→ᶜ T
Prᶜ {G = G} h = Ct.C Ct.π₁ (Ct.Ct (rememberᶜ G h))

----------------------------------------------------------------------
-- Raw translations
----------------------------------------------------------------------

toPr : ∀ {T U} → T Ct.→ᶜ U → T Pr.→ᴾ U
toPr Ct.id = Pr.id
toPr (Ct.C f g) = Pr.C (toPr f) (toPr g)
toPr Ct.`⊤ = Pr.`⊤
toPr Ct.`⊥ = Pr.`⊥
toPr (Ct.`# f g) = Pr.`# (toPr f) (toPr g)
toPr Ct.π₁ = Pr.π₁
toPr Ct.π₂ = Pr.π₂
toPr Ct.ι₁ = Pr.ι₁
toPr Ct.ι₂ = Pr.ι₂
toPr (Ct.`case f g) = Pr.`case (toPr f) (toPr g)
toPr (Ct.lam f) = Pr.lam (toPr f)
toPr Ct.apply = Pr.apply
toPr (Ct.fmap G f) = Pr.fmap G (toPr f)
toPr (Ct.strength G) = Pr.strength G
toPr Ct.con = Pr.con
toPr (Ct.Ct {G = G} h) = Ctᴾʳ (toPr h)

toCt : ∀ {T U} → T Pr.→ᴾ U → T Ct.→ᶜ U
toCt Pr.id = Ct.id
toCt (Pr.C f g) = Ct.C (toCt f) (toCt g)
toCt Pr.`⊤ = Ct.`⊤
toCt Pr.`⊥ = Ct.`⊥
toCt (Pr.`# f g) = Ct.`# (toCt f) (toCt g)
toCt Pr.π₁ = Ct.π₁
toCt Pr.π₂ = Ct.π₂
toCt Pr.ι₁ = Ct.ι₁
toCt Pr.ι₂ = Ct.ι₂
toCt (Pr.`case f g) = Ct.`case (toCt f) (toCt g)
toCt (Pr.lam f) = Ct.lam (toCt f)
toCt Pr.apply = Ct.apply
toCt (Pr.fmap G f) = Ct.fmap G (toCt f)
toCt (Pr.strength G) = Ct.strength G
toCt Pr.con = Ct.con
toCt {T = ind G `× U} {U = T} (Pr.Pr h) = Prᶜ (toCt h)

toPr-fmapᶜ : ∀ {T U G} (S : StructuralFunctor G) (f : T Ct.→ᶜ U) →
  toPr (Ct.fmapᶜ S f) ≡ Pr.fmapᶜ S (toPr f)
toPr-fmapᶜ sf-𝟘 f = refl
toPr-fmapᶜ sf-𝟙 f = refl
toPr-fmapᶜ sf-var f = refl
toPr-fmapᶜ (sf-× S R) f
  rewrite toPr-fmapᶜ S f | toPr-fmapᶜ R f = refl
toPr-fmapᶜ (sf-+ S R) f
  rewrite toPr-fmapᶜ S f | toPr-fmapᶜ R f = refl
toPr-fmapᶜ (sf-⇒ A S) f
  rewrite toPr-fmapᶜ S f = refl

toPr-strengthᶜ : ∀ {T U G} (S : StructuralFunctor G) →
  toPr (Ct.strengthᶜ {T = T} {U = U} S) ≡ Pr.strengthᶜ S
toPr-strengthᶜ sf-𝟘 = refl
toPr-strengthᶜ sf-𝟙 = refl
toPr-strengthᶜ sf-var = refl
toPr-strengthᶜ {T = T} {U = U} (sf-× S R)
  rewrite toPr-strengthᶜ {T = T} {U = U} S
        | toPr-strengthᶜ {T = T} {U = U} R = refl
toPr-strengthᶜ {T = T} {U = U} (sf-+ S R)
  rewrite toPr-strengthᶜ {T = T} {U = U} S
        | toPr-strengthᶜ {T = T} {U = U} R = refl
toPr-strengthᶜ {T = T} {U = U} (sf-⇒ A S)
  rewrite toPr-strengthᶜ {T = T} {U = U} S = refl

toCt-fmapᶜ : ∀ {T U G} (S : StructuralFunctor G) (f : T Pr.→ᴾ U) →
  toCt (Pr.fmapᶜ S f) ≡ Ct.fmapᶜ S (toCt f)
toCt-fmapᶜ sf-𝟘 f = refl
toCt-fmapᶜ sf-𝟙 f = refl
toCt-fmapᶜ sf-var f = refl
toCt-fmapᶜ (sf-× S R) f
  rewrite toCt-fmapᶜ S f | toCt-fmapᶜ R f = refl
toCt-fmapᶜ (sf-+ S R) f
  rewrite toCt-fmapᶜ S f | toCt-fmapᶜ R f = refl
toCt-fmapᶜ (sf-⇒ A S) f
  rewrite toCt-fmapᶜ S f = refl

toCt-strengthᶜ : ∀ {T U G} (S : StructuralFunctor G) →
  toCt (Pr.strengthᶜ {T = T} {U = U} S) ≡ Ct.strengthᶜ S
toCt-strengthᶜ sf-𝟘 = refl
toCt-strengthᶜ sf-𝟙 = refl
toCt-strengthᶜ sf-var = refl
toCt-strengthᶜ {T = T} {U = U} (sf-× S R)
  rewrite toCt-strengthᶜ {T = T} {U = U} S
        | toCt-strengthᶜ {T = T} {U = U} R = refl
toCt-strengthᶜ {T = T} {U = U} (sf-+ S R)
  rewrite toCt-strengthᶜ {T = T} {U = U} S
        | toCt-strengthᶜ {T = T} {U = U} R = refl
toCt-strengthᶜ {T = T} {U = U} (sf-⇒ A S)
  rewrite toCt-strengthᶜ {T = T} {U = U} S = refl

----------------------------------------------------------------------
-- Equation preservation: catamorphism-primitive into paramorphism-primitive
----------------------------------------------------------------------

catamorphismArgsᴾ : (G : Ty HO 1) → (Pr.ind G Pr.`× U Pr.→ᴾ T)
  → (G [ Pr.ind G ]) Pr.`× U Pr.→ᴾ (G [ T ]) Pr.`× U
catamorphismArgsᴾ G p = Pr.`# (Pr.pmap G p) Pr.π₂

dropLayerᴾ : ∀ {T} (G : Ty HO 1) {U : TY HO} →
  (G [ T Pr.`× Pr.ind G ]) Pr.`× U Pr.→ᴾ (G [ T ]) Pr.`× U
dropLayerᴾ G = Pr.`# (Pr.C (Pr.fmap G Pr.π₁) Pr.π₁) Pr.π₂

C-#ᴾ : ∀ {A B D E : TY HO}
  {f : B Pr.→ᴾ D} {g : B Pr.→ᴾ E} {h : A Pr.→ᴾ B} →
  Pr.C (Pr.`# f g) h PEq.≈ Pr.`# (Pr.C f h) (Pr.C g h)
C-#ᴾ =
  PEq.≈-trans (PEq.≈-sym PEq.×-η)
    (PEq.`#-cong
      (PEq.≈-trans PEq.C-assoc (PEq.C-cong PEq.×-β₁ PEq.≈-refl))
      (PEq.≈-trans PEq.C-assoc (PEq.C-cong PEq.×-β₂ PEq.≈-refl)))

drop-first-paraArgsᴾ : ∀ {T U} (G : Ty HO 1)
  (p : Pr.ind G Pr.`× U Pr.→ᴾ T) →
  Pr.C (Pr.C (Pr.fmap G Pr.π₁) Pr.π₁) (Pr.paraArgs G p)
  PEq.≈ Pr.pmap G p
drop-first-paraArgsᴾ G p =
  PEq.≈-trans (PEq.≈-sym PEq.C-assoc)
    (PEq.≈-trans
      (PEq.C-cong PEq.≈-refl PEq.×-β₁)
      (PEq.≈-trans PEq.C-assoc
        (PEq.C-cong
          (PEq.≈-trans
            (PEq.≈-sym (PEq.fmap-C G))
            (PEq.fmap-cong G PEq.×-β₁))
          PEq.≈-refl)))

dropLayer-paraArgsᴾ : ∀ {T U} (G : Ty HO 1)
  (p : Pr.ind G Pr.`× U Pr.→ᴾ T) →
  Pr.C (dropLayerᴾ G) (Pr.paraArgs G p) PEq.≈ catamorphismArgsᴾ G p
dropLayer-paraArgsᴾ G p =
  PEq.≈-trans C-#ᴾ
    (PEq.`#-cong (drop-first-paraArgsᴾ G p) PEq.×-β₂)

dropSubterm-paraArgsᴾ : ∀ {T U} (G : Ty HO 1)
  (h : (G [ T ]) Pr.`× U Pr.→ᴾ T)
  (p : Pr.ind G Pr.`× U Pr.→ᴾ T) →
  Pr.C (dropSubtermᴾ G h) (Pr.paraArgs G p)
  PEq.≈ Pr.C h (catamorphismArgsᴾ G p)
dropSubterm-paraArgsᴾ G h p =
  PEq.≈-trans (PEq.≈-sym PEq.C-assoc)
    (PEq.C-cong PEq.≈-refl (dropLayer-paraArgsᴾ G p))

Ctᴾʳ-β : ∀ {T U} {G : Ty HO 1}
  {h : (G [ T ]) Pr.`× U Pr.→ᴾ T} →
  Pr.C (Ctᴾʳ {G = G} h) (Pr.map-× (Pr.con {G = G}) (Pr.id {T = U}))
  PEq.≈
  Pr.C h (catamorphismArgsᴾ G (Ctᴾʳ {G = G} h))
Ctᴾʳ-β {G = G} {h = h} =
  PEq.≈-trans PEq.Pr-β
    (dropSubterm-paraArgsᴾ G h (Ctᴾʳ h))

Ctᴾʳ-unique : ∀ {T U} {G : Ty HO 1}
  {h : (G [ T ]) Pr.`× U Pr.→ᴾ T}
  {p : Pr.ind G Pr.`× U Pr.→ᴾ T} →
  Pr.C p (Pr.map-× (Pr.con {G = G}) (Pr.id {T = U}))
  PEq.≈ Pr.C h (catamorphismArgsᴾ G p) →
  p PEq.≈ Ctᴾʳ {G = G} h
Ctᴾʳ-unique {G = G} {h = h} premise =
  PEq.Pr-unique
    (PEq.≈-trans premise
      (PEq.≈-sym (dropSubterm-paraArgsᴾ G h _)))

toPr-preserves : ∀ {T U} {f g : T Ct.→ᶜ U} →
  f CtEq.≈ g → toPr f PEq.≈ toPr g
toPr-preserves CtEq.≈-refl = PEq.≈-refl
toPr-preserves (CtEq.≈-sym p) = PEq.≈-sym (toPr-preserves p)
toPr-preserves (CtEq.≈-trans p q) =
  PEq.≈-trans (toPr-preserves p) (toPr-preserves q)
toPr-preserves (CtEq.C-cong p q) =
  PEq.C-cong (toPr-preserves p) (toPr-preserves q)
toPr-preserves (CtEq.`#-cong p q) =
  PEq.`#-cong (toPr-preserves p) (toPr-preserves q)
toPr-preserves (CtEq.`case-cong p q) =
  PEq.`case-cong (toPr-preserves p) (toPr-preserves q)
toPr-preserves (CtEq.lam-cong p) =
  PEq.lam-cong (toPr-preserves p)
toPr-preserves (CtEq.fmap-cong G p) =
  PEq.fmap-cong G (toPr-preserves p)
toPr-preserves (CtEq.Ct-cong {H = H} p) =
  PEq.Pr-cong (PEq.C-cong (toPr-preserves p) PEq.≈-refl)
toPr-preserves CtEq.C-idˡ = PEq.C-idˡ
toPr-preserves CtEq.C-idʳ = PEq.C-idʳ
toPr-preserves CtEq.C-assoc = PEq.C-assoc
toPr-preserves (CtEq.fmap-id G) = PEq.fmap-id G
toPr-preserves (CtEq.fmap-C G) = PEq.fmap-C G
toPr-preserves (CtEq.fmap-βᶜ S {f = f})
  rewrite toPr-fmapᶜ S f = PEq.fmap-βᶜ S
toPr-preserves (CtEq.strength-naturalˡ G) = PEq.strength-naturalˡ G
toPr-preserves (CtEq.strength-naturalʳ G) = PEq.strength-naturalʳ G
toPr-preserves (CtEq.strength-π₁ G) = PEq.strength-π₁ G
toPr-preserves (CtEq.strength-βᶜ {A = A} {B = B} S)
  rewrite toPr-strengthᶜ {T = A} {U = B} S = PEq.strength-βᶜ S
toPr-preserves CtEq.𝟙-unique = PEq.𝟙-unique
toPr-preserves CtEq.𝟘-unique = PEq.𝟘-unique
toPr-preserves CtEq.×-β₁ = PEq.×-β₁
toPr-preserves CtEq.×-β₂ = PEq.×-β₂
toPr-preserves CtEq.×-η = PEq.×-η
toPr-preserves CtEq.+-β₁ = PEq.+-β₁
toPr-preserves CtEq.+-β₂ = PEq.+-β₂
toPr-preserves CtEq.+-η = PEq.+-η
toPr-preserves CtEq.⇒-β = PEq.⇒-β
toPr-preserves CtEq.⇒-η = PEq.⇒-η
toPr-preserves (CtEq.Ct-β {H = H} {h = h}) =
  Ctᴾʳ-β {G = H} {h = toPr h}
toPr-preserves (CtEq.Ct-unique p) =
  Ctᴾʳ-unique (toPr-preserves p)

----------------------------------------------------------------------
-- Equation preservation: paramorphism-primitive into catamorphism-primitive
----------------------------------------------------------------------

paraArgsᶜ : (G : Ty HO 1) → (Ct.ind G Ct.`× U Ct.→ᶜ T)
  → (G [ Ct.ind G ]) Ct.`× U Ct.→ᶜ (G [ T Ct.`× Ct.ind G ]) Ct.`× U
paraArgsᶜ G p = Ct.`# (Ct.pmap G (Ct.`# p Ct.π₁)) Ct.π₂

rebuild₀ᶜ : ∀ {U} (G : Ty HO 1) →
  (G [ Ct.ind G ]) Ct.`× U Ct.→ᶜ Ct.ind G
rebuild₀ᶜ G = Ct.C Ct.con Ct.π₁

C-#ᶜ : ∀ {A B D E : TY HO}
  {f : B Ct.→ᶜ D} {g : B Ct.→ᶜ E} {h : A Ct.→ᶜ B} →
  Ct.C (Ct.`# f g) h CtEq.≈ Ct.`# (Ct.C f h) (Ct.C g h)
C-#ᶜ =
  CtEq.≈-trans (CtEq.≈-sym CtEq.×-η)
    (CtEq.`#-cong
      (CtEq.≈-trans CtEq.C-assoc (CtEq.C-cong CtEq.×-β₁ CtEq.≈-refl))
      (CtEq.≈-trans CtEq.C-assoc (CtEq.C-cong CtEq.×-β₂ CtEq.≈-refl)))

pmap-congᶜ : ∀ {A B U : TY HO} (G : Ty HO 1)
  {f f′ : A Ct.`× U Ct.→ᶜ B} →
  f CtEq.≈ f′ → Ct.pmap G f CtEq.≈ Ct.pmap G f′
pmap-congᶜ G f≈ =
  CtEq.C-cong (CtEq.fmap-cong G f≈) CtEq.≈-refl

catamorphismArgs-congᶜ : ∀ {T U} (G : Ty HO 1)
  {p p′ : Ct.ind G Ct.`× U Ct.→ᶜ T} →
  p CtEq.≈ p′ → Ct.catamorphismArgs G p CtEq.≈ Ct.catamorphismArgs G p′
catamorphismArgs-congᶜ G p≈ =
  CtEq.`#-cong (pmap-congᶜ G p≈) CtEq.≈-refl

pmap-Cᶜ : ∀ {A B D U : TY HO} (G : Ty HO 1)
  {f : B Ct.→ᶜ D} {g : A Ct.`× U Ct.→ᶜ B} →
  Ct.C (Ct.fmap G f) (Ct.pmap G g) CtEq.≈ Ct.pmap G (Ct.C f g)
pmap-Cᶜ G =
  CtEq.≈-trans CtEq.C-assoc
    (CtEq.C-cong (CtEq.≈-sym (CtEq.fmap-C G)) CtEq.≈-refl)

π₁-con-mapᶜ : ∀ {U} {G : Ty HO 1} →
  Ct.C Ct.π₁ (Ct.map-× (Ct.con {G = G}) (Ct.id {T = U}))
  CtEq.≈ Ct.C Ct.con Ct.π₁
π₁-con-mapᶜ = CtEq.×-β₁

rebuild₀-catamorphismArgs-π₁ᶜ : ∀ {U} (G : Ty HO 1) →
  Ct.C (rebuild₀ᶜ {U = U} G) (Ct.catamorphismArgs G Ct.π₁)
  CtEq.≈ Ct.C Ct.con Ct.π₁
rebuild₀-catamorphismArgs-π₁ᶜ G =
  CtEq.≈-trans (CtEq.≈-sym CtEq.C-assoc)
    (CtEq.≈-trans
      (CtEq.C-cong CtEq.≈-refl CtEq.×-β₁)
      (CtEq.C-cong CtEq.≈-refl (CtEq.strength-π₁ G)))

π₁-is-Ct-rebuild₀ᶜ : ∀ {U} (G : Ty HO 1) →
  Ct.π₁ CtEq.≈ Ct.Ct {G = G} {T = Ct.ind G} {U = U} (rebuild₀ᶜ G)
π₁-is-Ct-rebuild₀ᶜ {U = U} G =
  CtEq.Ct-unique
    (CtEq.≈-trans π₁-con-mapᶜ
      (CtEq.≈-sym (rebuild₀-catamorphismArgs-π₁ᶜ {U = U} G)))

rebuild-catamorphismArgsᶜ : ∀ {T U} (G : Ty HO 1)
  (r : Ct.ind G Ct.`× U Ct.→ᶜ T Ct.`× Ct.ind G) →
  Ct.C (rebuildᶜ G) (Ct.catamorphismArgs G r)
  CtEq.≈
  Ct.C (rebuild₀ᶜ G) (Ct.catamorphismArgs G (Ct.C Ct.π₂ r))
rebuild-catamorphismArgsᶜ G r =
  CtEq.≈-trans (CtEq.≈-sym CtEq.C-assoc)
    (CtEq.≈-trans
      (CtEq.C-cong CtEq.≈-refl (CtEq.≈-sym CtEq.C-assoc))
      (CtEq.≈-trans
        (CtEq.C-cong CtEq.≈-refl
          (CtEq.C-cong CtEq.≈-refl CtEq.×-β₁))
        (CtEq.≈-trans
          (CtEq.C-cong CtEq.≈-refl (pmap-Cᶜ G))
          (CtEq.≈-trans
            (CtEq.C-cong CtEq.≈-refl (CtEq.≈-sym CtEq.×-β₁))
            CtEq.C-assoc))))

second-is-Ct-rebuild₀ᶜ : ∀ {T U} {G : Ty HO 1}
  (h : (G [ T Ct.`× Ct.ind G ]) Ct.`× U Ct.→ᶜ T) →
  Ct.C Ct.π₂ (Ct.Ct (rememberᶜ G h))
  CtEq.≈ Ct.Ct {G = G} {T = Ct.ind G} {U = U} (rebuild₀ᶜ G)
second-is-Ct-rebuild₀ᶜ {G = G} h =
  CtEq.Ct-unique
    (CtEq.≈-trans (CtEq.≈-sym CtEq.C-assoc)
      (CtEq.≈-trans
        (CtEq.C-cong CtEq.≈-refl CtEq.Ct-β)
        (CtEq.≈-trans CtEq.C-assoc
          (CtEq.≈-trans
            (CtEq.C-cong CtEq.×-β₂ CtEq.≈-refl)
            (rebuild-catamorphismArgsᶜ G (Ct.Ct (rememberᶜ G h)))))))

remember-secondᶜ : ∀ {T U} {G : Ty HO 1}
  (h : (G [ T Ct.`× Ct.ind G ]) Ct.`× U Ct.→ᶜ T) →
  Ct.C Ct.π₂ (Ct.Ct (rememberᶜ G h)) CtEq.≈ Ct.π₁
remember-secondᶜ {G = G} h =
  CtEq.≈-trans (second-is-Ct-rebuild₀ᶜ h)
    (CtEq.≈-sym (π₁-is-Ct-rebuild₀ᶜ G))

remember-ηᶜ : ∀ {T U} {G : Ty HO 1}
  (h : (G [ T Ct.`× Ct.ind G ]) Ct.`× U Ct.→ᶜ T) →
  Ct.Ct (rememberᶜ G h) CtEq.≈ Ct.`# (Prᶜ h) Ct.π₁
remember-ηᶜ h =
  CtEq.≈-trans (CtEq.≈-sym CtEq.×-η)
    (CtEq.`#-cong CtEq.≈-refl (remember-secondᶜ h))

catamorphismArgs-rememberᶜ : ∀ {T U} {G : Ty HO 1}
  (h : (G [ T Ct.`× Ct.ind G ]) Ct.`× U Ct.→ᶜ T) →
  Ct.catamorphismArgs G (Ct.Ct (rememberᶜ G h)) CtEq.≈ paraArgsᶜ G (Prᶜ h)
catamorphismArgs-rememberᶜ {G = G} h =
  catamorphismArgs-congᶜ G (remember-ηᶜ h)

Prᶜ-β : ∀ {T U} {G : Ty HO 1}
  {h : (G [ T Ct.`× Ct.ind G ]) Ct.`× U Ct.→ᶜ T} →
  Ct.C (Prᶜ {G = G} h) (Ct.map-× (Ct.con {G = G}) (Ct.id {T = U}))
  CtEq.≈
  Ct.C h (paraArgsᶜ G (Prᶜ {G = G} h))
Prᶜ-β {G = G} {h = h} =
  CtEq.≈-trans (CtEq.≈-sym CtEq.C-assoc)
    (CtEq.≈-trans
      (CtEq.C-cong CtEq.≈-refl CtEq.Ct-β)
      (CtEq.≈-trans CtEq.C-assoc
        (CtEq.≈-trans
          (CtEq.C-cong CtEq.×-β₁ CtEq.≈-refl)
          (CtEq.C-cong CtEq.≈-refl (catamorphismArgs-rememberᶜ h)))))

rebuild-paraArgsᶜ : ∀ {T U} (G : Ty HO 1)
  (p : Ct.ind G Ct.`× U Ct.→ᶜ T) →
  Ct.C (rebuildᶜ G) (paraArgsᶜ G p) CtEq.≈ Ct.C Ct.con Ct.π₁
rebuild-paraArgsᶜ G p =
  CtEq.≈-trans (rebuild-catamorphismArgsᶜ G (Ct.`# p Ct.π₁))
    (CtEq.≈-trans
      (CtEq.C-cong CtEq.≈-refl
        (catamorphismArgs-congᶜ G CtEq.×-β₂))
      (rebuild₀-catamorphismArgs-π₁ᶜ G))

Prᶜ-unique : ∀ {T U} {G : Ty HO 1}
  {h : (G [ T Ct.`× Ct.ind G ]) Ct.`× U Ct.→ᶜ T}
  {p : Ct.ind G Ct.`× U Ct.→ᶜ T} →
  Ct.C p (Ct.map-× (Ct.con {G = G}) (Ct.id {T = U}))
  CtEq.≈ Ct.C h (paraArgsᶜ G p) →
  p CtEq.≈ Prᶜ {G = G} h
Prᶜ-unique {G = G} {h = h} {p = p} premise =
  CtEq.≈-trans (CtEq.≈-sym CtEq.×-β₁)
    (CtEq.C-cong CtEq.≈-refl
      (CtEq.Ct-unique
        (CtEq.≈-trans C-#ᶜ
          (CtEq.≈-trans
            (CtEq.`#-cong premise
              (CtEq.≈-trans π₁-con-mapᶜ
                (CtEq.≈-sym (rebuild-paraArgsᶜ G p))))
            (CtEq.≈-sym C-#ᶜ)))))

toCt-preserves : ∀ {T U} {f g : T Pr.→ᴾ U} →
  f PEq.≈ g → toCt f CtEq.≈ toCt g
toCt-preserves PEq.≈-refl = CtEq.≈-refl
toCt-preserves (PEq.≈-sym p) = CtEq.≈-sym (toCt-preserves p)
toCt-preserves (PEq.≈-trans p q) =
  CtEq.≈-trans (toCt-preserves p) (toCt-preserves q)
toCt-preserves (PEq.C-cong p q) =
  CtEq.C-cong (toCt-preserves p) (toCt-preserves q)
toCt-preserves (PEq.`#-cong p q) =
  CtEq.`#-cong (toCt-preserves p) (toCt-preserves q)
toCt-preserves (PEq.`case-cong p q) =
  CtEq.`case-cong (toCt-preserves p) (toCt-preserves q)
toCt-preserves (PEq.lam-cong p) =
  CtEq.lam-cong (toCt-preserves p)
toCt-preserves (PEq.fmap-cong G p) =
  CtEq.fmap-cong G (toCt-preserves p)
toCt-preserves (PEq.Pr-cong {H = H} p) =
  CtEq.C-cong CtEq.≈-refl
    (CtEq.Ct-cong (CtEq.`#-cong (toCt-preserves p) CtEq.≈-refl))
toCt-preserves PEq.C-idˡ = CtEq.C-idˡ
toCt-preserves PEq.C-idʳ = CtEq.C-idʳ
toCt-preserves PEq.C-assoc = CtEq.C-assoc
toCt-preserves (PEq.fmap-id G) = CtEq.fmap-id G
toCt-preserves (PEq.fmap-C G) = CtEq.fmap-C G
toCt-preserves (PEq.fmap-βᶜ S {f = f})
  rewrite toCt-fmapᶜ S f = CtEq.fmap-βᶜ S
toCt-preserves (PEq.strength-naturalˡ G) = CtEq.strength-naturalˡ G
toCt-preserves (PEq.strength-naturalʳ G) = CtEq.strength-naturalʳ G
toCt-preserves (PEq.strength-π₁ G) = CtEq.strength-π₁ G
toCt-preserves (PEq.strength-βᶜ {A = A} {B = B} S)
  rewrite toCt-strengthᶜ {T = A} {U = B} S = CtEq.strength-βᶜ S
toCt-preserves PEq.𝟙-unique = CtEq.𝟙-unique
toCt-preserves PEq.𝟘-unique = CtEq.𝟘-unique
toCt-preserves PEq.×-β₁ = CtEq.×-β₁
toCt-preserves PEq.×-β₂ = CtEq.×-β₂
toCt-preserves PEq.×-η = CtEq.×-η
toCt-preserves PEq.+-β₁ = CtEq.+-β₁
toCt-preserves PEq.+-β₂ = CtEq.+-β₂
toCt-preserves PEq.+-η = CtEq.+-η
toCt-preserves PEq.⇒-β = CtEq.⇒-β
toCt-preserves PEq.⇒-η = CtEq.⇒-η
toCt-preserves (PEq.Pr-β {H = H} {h = h}) =
  Prᶜ-β {G = H} {h = toCt h}
toCt-preserves (PEq.Pr-unique p) =
  Prᶜ-unique (toCt-preserves p)

----------------------------------------------------------------------
-- Round trips up to the respective equational theories
----------------------------------------------------------------------

toPr-toCt : ∀ {T U} (f : T Pr.→ᴾ U) → toPr (toCt f) PEq.≈ f
toPr-toCt Pr.id = PEq.≈-refl
toPr-toCt (Pr.C f g) = PEq.C-cong (toPr-toCt f) (toPr-toCt g)
toPr-toCt Pr.`⊤ = PEq.≈-refl
toPr-toCt Pr.`⊥ = PEq.≈-refl
toPr-toCt (Pr.`# f g) = PEq.`#-cong (toPr-toCt f) (toPr-toCt g)
toPr-toCt Pr.π₁ = PEq.≈-refl
toPr-toCt Pr.π₂ = PEq.≈-refl
toPr-toCt Pr.ι₁ = PEq.≈-refl
toPr-toCt Pr.ι₂ = PEq.≈-refl
toPr-toCt (Pr.`case f g) = PEq.`case-cong (toPr-toCt f) (toPr-toCt g)
toPr-toCt (Pr.lam f) = PEq.lam-cong (toPr-toCt f)
toPr-toCt Pr.apply = PEq.≈-refl
toPr-toCt (Pr.fmap G f) = PEq.fmap-cong G (toPr-toCt f)
toPr-toCt (Pr.strength G) = PEq.≈-refl
toPr-toCt Pr.con = PEq.≈-refl
toPr-toCt {T = ind G `× U} {U = T} (Pr.Pr h) =
  PEq.Pr-unique
    (PEq.≈-trans
      (toPr-preserves (Prᶜ-β {G = G} {h = toCt h}))
      (PEq.C-cong (toPr-toCt h) PEq.≈-refl))

toCt-toPr : ∀ {T U} (f : T Ct.→ᶜ U) → toCt (toPr f) CtEq.≈ f
toCt-toPr Ct.id = CtEq.≈-refl
toCt-toPr (Ct.C f g) = CtEq.C-cong (toCt-toPr f) (toCt-toPr g)
toCt-toPr Ct.`⊤ = CtEq.≈-refl
toCt-toPr Ct.`⊥ = CtEq.≈-refl
toCt-toPr (Ct.`# f g) = CtEq.`#-cong (toCt-toPr f) (toCt-toPr g)
toCt-toPr Ct.π₁ = CtEq.≈-refl
toCt-toPr Ct.π₂ = CtEq.≈-refl
toCt-toPr Ct.ι₁ = CtEq.≈-refl
toCt-toPr Ct.ι₂ = CtEq.≈-refl
toCt-toPr (Ct.`case f g) = CtEq.`case-cong (toCt-toPr f) (toCt-toPr g)
toCt-toPr (Ct.lam f) = CtEq.lam-cong (toCt-toPr f)
toCt-toPr Ct.apply = CtEq.≈-refl
toCt-toPr (Ct.fmap G f) = CtEq.fmap-cong G (toCt-toPr f)
toCt-toPr (Ct.strength G) = CtEq.≈-refl
toCt-toPr Ct.con = CtEq.≈-refl
toCt-toPr (Ct.Ct {G = G} h) =
  CtEq.Ct-unique
    (CtEq.≈-trans
      (toCt-preserves (Ctᴾʳ-β {G = G} {h = toPr h}))
      (CtEq.C-cong (toCt-toPr h) CtEq.≈-refl))
