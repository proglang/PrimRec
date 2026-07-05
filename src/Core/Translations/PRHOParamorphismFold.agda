{-# OPTIONS --safe #-}

module Core.Translations.PRHOParamorphismFold where

import Core.PRHO as P
import Core.PRHOFold as F
import Core.Equations.PRHO as PEq
import Core.Equations.PRHOFold as FEq
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Core.Types

variable
  W : TY HO

----------------------------------------------------------------------
-- Derived eliminators
----------------------------------------------------------------------

dropSubtermᴾ : ∀ {T U} (G : Ty HO 1) →
  (G [ T ]) P.`× U P.→ᴾ T →
  (G [ T P.`× P.ind G ]) P.`× U P.→ᴾ T
dropSubtermᴾ G h =
  P.C h (P.`# (P.C (P.fmap G P.π₁) P.π₁) P.π₂)

Fᴾ : ∀ {T U} {G : Ty HO 1} →
  (G [ T ]) P.`× U P.→ᴾ T →
  P.ind G P.`× U P.→ᴾ T
Fᴾ {G = G} h = P.P (dropSubtermᴾ G h)

rebuildᶠ : ∀ {T U} (G : Ty HO 1) →
  (G [ T F.`× F.ind G ]) F.`× U F.→ᶠ F.ind G
rebuildᶠ G =
  F.C F.con (F.C (F.fmap G F.π₂) F.π₁)

rememberᶠ : ∀ {T U} (G : Ty HO 1) →
  (G [ T F.`× F.ind G ]) F.`× U F.→ᶠ T →
  (G [ T F.`× F.ind G ]) F.`× U F.→ᶠ T F.`× F.ind G
rememberᶠ G h = F.`# h (rebuildᶠ G)

Pᶠ : ∀ {T U} {G : Ty HO 1} →
  (G [ T F.`× F.ind G ]) F.`× U F.→ᶠ T →
  F.ind G F.`× U F.→ᶠ T
Pᶠ {G = G} h = F.C F.π₁ (F.F (rememberᶠ G h))

----------------------------------------------------------------------
-- Raw translations
----------------------------------------------------------------------

toP : ∀ {T U} → T F.→ᶠ U → T P.→ᴾ U
toP F.id = P.id
toP (F.C f g) = P.C (toP f) (toP g)
toP F.`⊤ = P.`⊤
toP F.`⊥ = P.`⊥
toP (F.`# f g) = P.`# (toP f) (toP g)
toP F.π₁ = P.π₁
toP F.π₂ = P.π₂
toP F.ι₁ = P.ι₁
toP F.ι₂ = P.ι₂
toP (F.`case f g) = P.`case (toP f) (toP g)
toP (F.lam f) = P.lam (toP f)
toP F.apply = P.apply
toP (F.fmap G f) = P.fmap G (toP f)
toP (F.strength G) = P.strength G
toP F.con = P.con
toP (F.F {G = G} h) = Fᴾ (toP h)

toF : ∀ {T U} → T P.→ᴾ U → T F.→ᶠ U
toF P.id = F.id
toF (P.C f g) = F.C (toF f) (toF g)
toF P.`⊤ = F.`⊤
toF P.`⊥ = F.`⊥
toF (P.`# f g) = F.`# (toF f) (toF g)
toF P.π₁ = F.π₁
toF P.π₂ = F.π₂
toF P.ι₁ = F.ι₁
toF P.ι₂ = F.ι₂
toF (P.`case f g) = F.`case (toF f) (toF g)
toF (P.lam f) = F.lam (toF f)
toF P.apply = F.apply
toF (P.fmap G f) = F.fmap G (toF f)
toF (P.strength G) = F.strength G
toF P.con = F.con
toF {T = ind G `× U} {U = T} (P.P h) = Pᶠ (toF h)

toP-fmapᶜ : ∀ {T U G} (S : StructuralFunctor G) (f : T F.→ᶠ U) →
  toP (F.fmapᶜ S f) ≡ P.fmapᶜ S (toP f)
toP-fmapᶜ sf-𝟘 f = refl
toP-fmapᶜ sf-𝟙 f = refl
toP-fmapᶜ sf-var f = refl
toP-fmapᶜ (sf-× S R) f
  rewrite toP-fmapᶜ S f | toP-fmapᶜ R f = refl
toP-fmapᶜ (sf-+ S R) f
  rewrite toP-fmapᶜ S f | toP-fmapᶜ R f = refl
toP-fmapᶜ (sf-⇒ A S) f
  rewrite toP-fmapᶜ S f = refl

toP-strengthᶜ : ∀ {T U G} (S : StructuralFunctor G) →
  toP (F.strengthᶜ {T = T} {U = U} S) ≡ P.strengthᶜ S
toP-strengthᶜ sf-𝟘 = refl
toP-strengthᶜ sf-𝟙 = refl
toP-strengthᶜ sf-var = refl
toP-strengthᶜ {T = T} {U = U} (sf-× S R)
  rewrite toP-strengthᶜ {T = T} {U = U} S
        | toP-strengthᶜ {T = T} {U = U} R = refl
toP-strengthᶜ {T = T} {U = U} (sf-+ S R)
  rewrite toP-strengthᶜ {T = T} {U = U} S
        | toP-strengthᶜ {T = T} {U = U} R = refl
toP-strengthᶜ {T = T} {U = U} (sf-⇒ A S)
  rewrite toP-strengthᶜ {T = T} {U = U} S = refl

toF-fmapᶜ : ∀ {T U G} (S : StructuralFunctor G) (f : T P.→ᴾ U) →
  toF (P.fmapᶜ S f) ≡ F.fmapᶜ S (toF f)
toF-fmapᶜ sf-𝟘 f = refl
toF-fmapᶜ sf-𝟙 f = refl
toF-fmapᶜ sf-var f = refl
toF-fmapᶜ (sf-× S R) f
  rewrite toF-fmapᶜ S f | toF-fmapᶜ R f = refl
toF-fmapᶜ (sf-+ S R) f
  rewrite toF-fmapᶜ S f | toF-fmapᶜ R f = refl
toF-fmapᶜ (sf-⇒ A S) f
  rewrite toF-fmapᶜ S f = refl

toF-strengthᶜ : ∀ {T U G} (S : StructuralFunctor G) →
  toF (P.strengthᶜ {T = T} {U = U} S) ≡ F.strengthᶜ S
toF-strengthᶜ sf-𝟘 = refl
toF-strengthᶜ sf-𝟙 = refl
toF-strengthᶜ sf-var = refl
toF-strengthᶜ {T = T} {U = U} (sf-× S R)
  rewrite toF-strengthᶜ {T = T} {U = U} S
        | toF-strengthᶜ {T = T} {U = U} R = refl
toF-strengthᶜ {T = T} {U = U} (sf-+ S R)
  rewrite toF-strengthᶜ {T = T} {U = U} S
        | toF-strengthᶜ {T = T} {U = U} R = refl
toF-strengthᶜ {T = T} {U = U} (sf-⇒ A S)
  rewrite toF-strengthᶜ {T = T} {U = U} S = refl

----------------------------------------------------------------------
-- Equation preservation: fold-primitive into paramorphism-primitive
----------------------------------------------------------------------

foldArgsᴾ : (G : Ty HO 1) → (P.ind G P.`× U P.→ᴾ T)
  → (G [ P.ind G ]) P.`× U P.→ᴾ (G [ T ]) P.`× U
foldArgsᴾ G p = P.`# (P.pmap G p) P.π₂

dropLayerᴾ : ∀ {T} (G : Ty HO 1) {U : TY HO} →
  (G [ T P.`× P.ind G ]) P.`× U P.→ᴾ (G [ T ]) P.`× U
dropLayerᴾ G = P.`# (P.C (P.fmap G P.π₁) P.π₁) P.π₂

C-#ᴾ : ∀ {A B D E : TY HO}
  {f : B P.→ᴾ D} {g : B P.→ᴾ E} {h : A P.→ᴾ B} →
  P.C (P.`# f g) h PEq.≈ P.`# (P.C f h) (P.C g h)
C-#ᴾ =
  PEq.≈-trans (PEq.≈-sym PEq.×-η)
    (PEq.`#-cong
      (PEq.≈-trans PEq.C-assoc (PEq.C-cong PEq.×-β₁ PEq.≈-refl))
      (PEq.≈-trans PEq.C-assoc (PEq.C-cong PEq.×-β₂ PEq.≈-refl)))

drop-first-paraArgsᴾ : ∀ {T U} (G : Ty HO 1)
  (p : P.ind G P.`× U P.→ᴾ T) →
  P.C (P.C (P.fmap G P.π₁) P.π₁) (P.paraArgs G p)
  PEq.≈ P.pmap G p
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
  (p : P.ind G P.`× U P.→ᴾ T) →
  P.C (dropLayerᴾ G) (P.paraArgs G p) PEq.≈ foldArgsᴾ G p
dropLayer-paraArgsᴾ G p =
  PEq.≈-trans C-#ᴾ
    (PEq.`#-cong (drop-first-paraArgsᴾ G p) PEq.×-β₂)

dropSubterm-paraArgsᴾ : ∀ {T U} (G : Ty HO 1)
  (h : (G [ T ]) P.`× U P.→ᴾ T)
  (p : P.ind G P.`× U P.→ᴾ T) →
  P.C (dropSubtermᴾ G h) (P.paraArgs G p)
  PEq.≈ P.C h (foldArgsᴾ G p)
dropSubterm-paraArgsᴾ G h p =
  PEq.≈-trans (PEq.≈-sym PEq.C-assoc)
    (PEq.C-cong PEq.≈-refl (dropLayer-paraArgsᴾ G p))

Fᴾ-β : ∀ {T U} {G : Ty HO 1}
  {h : (G [ T ]) P.`× U P.→ᴾ T} →
  P.C (Fᴾ {G = G} h) (P.map-× (P.con {G = G}) (P.id {T = U}))
  PEq.≈
  P.C h (foldArgsᴾ G (Fᴾ {G = G} h))
Fᴾ-β {G = G} {h = h} =
  PEq.≈-trans PEq.P-β
    (dropSubterm-paraArgsᴾ G h (Fᴾ h))

Fᴾ-unique : ∀ {T U} {G : Ty HO 1}
  {h : (G [ T ]) P.`× U P.→ᴾ T}
  {p : P.ind G P.`× U P.→ᴾ T} →
  P.C p (P.map-× (P.con {G = G}) (P.id {T = U}))
  PEq.≈ P.C h (foldArgsᴾ G p) →
  p PEq.≈ Fᴾ {G = G} h
Fᴾ-unique {G = G} {h = h} premise =
  PEq.P-unique
    (PEq.≈-trans premise
      (PEq.≈-sym (dropSubterm-paraArgsᴾ G h _)))

toP-preserves : ∀ {T U} {f g : T F.→ᶠ U} →
  f FEq.≈ g → toP f PEq.≈ toP g
toP-preserves FEq.≈-refl = PEq.≈-refl
toP-preserves (FEq.≈-sym p) = PEq.≈-sym (toP-preserves p)
toP-preserves (FEq.≈-trans p q) =
  PEq.≈-trans (toP-preserves p) (toP-preserves q)
toP-preserves (FEq.C-cong p q) =
  PEq.C-cong (toP-preserves p) (toP-preserves q)
toP-preserves (FEq.`#-cong p q) =
  PEq.`#-cong (toP-preserves p) (toP-preserves q)
toP-preserves (FEq.`case-cong p q) =
  PEq.`case-cong (toP-preserves p) (toP-preserves q)
toP-preserves (FEq.lam-cong p) =
  PEq.lam-cong (toP-preserves p)
toP-preserves (FEq.fmap-cong G p) =
  PEq.fmap-cong G (toP-preserves p)
toP-preserves (FEq.F-cong {H = H} p) =
  PEq.P-cong (PEq.C-cong (toP-preserves p) PEq.≈-refl)
toP-preserves FEq.C-idˡ = PEq.C-idˡ
toP-preserves FEq.C-idʳ = PEq.C-idʳ
toP-preserves FEq.C-assoc = PEq.C-assoc
toP-preserves (FEq.fmap-id G) = PEq.fmap-id G
toP-preserves (FEq.fmap-C G) = PEq.fmap-C G
toP-preserves (FEq.fmap-βᶜ S {f = f})
  rewrite toP-fmapᶜ S f = PEq.fmap-βᶜ S
toP-preserves (FEq.strength-naturalˡ G) = PEq.strength-naturalˡ G
toP-preserves (FEq.strength-naturalʳ G) = PEq.strength-naturalʳ G
toP-preserves (FEq.strength-π₁ G) = PEq.strength-π₁ G
toP-preserves (FEq.strength-βᶜ {A = A} {B = B} S)
  rewrite toP-strengthᶜ {T = A} {U = B} S = PEq.strength-βᶜ S
toP-preserves FEq.𝟙-unique = PEq.𝟙-unique
toP-preserves FEq.𝟘-unique = PEq.𝟘-unique
toP-preserves FEq.×-β₁ = PEq.×-β₁
toP-preserves FEq.×-β₂ = PEq.×-β₂
toP-preserves FEq.×-η = PEq.×-η
toP-preserves FEq.+-β₁ = PEq.+-β₁
toP-preserves FEq.+-β₂ = PEq.+-β₂
toP-preserves FEq.+-η = PEq.+-η
toP-preserves FEq.⇒-β = PEq.⇒-β
toP-preserves FEq.⇒-η = PEq.⇒-η
toP-preserves (FEq.F-β {H = H} {h = h}) =
  Fᴾ-β {G = H} {h = toP h}
toP-preserves (FEq.F-unique p) =
  Fᴾ-unique (toP-preserves p)

----------------------------------------------------------------------
-- Equation preservation: paramorphism-primitive into fold-primitive
----------------------------------------------------------------------

paraArgsᶠ : (G : Ty HO 1) → (F.ind G F.`× U F.→ᶠ T)
  → (G [ F.ind G ]) F.`× U F.→ᶠ (G [ T F.`× F.ind G ]) F.`× U
paraArgsᶠ G p = F.`# (F.pmap G (F.`# p F.π₁)) F.π₂

rebuild₀ᶠ : ∀ {U} (G : Ty HO 1) →
  (G [ F.ind G ]) F.`× U F.→ᶠ F.ind G
rebuild₀ᶠ G = F.C F.con F.π₁

C-#ᶠ : ∀ {A B D E : TY HO}
  {f : B F.→ᶠ D} {g : B F.→ᶠ E} {h : A F.→ᶠ B} →
  F.C (F.`# f g) h FEq.≈ F.`# (F.C f h) (F.C g h)
C-#ᶠ =
  FEq.≈-trans (FEq.≈-sym FEq.×-η)
    (FEq.`#-cong
      (FEq.≈-trans FEq.C-assoc (FEq.C-cong FEq.×-β₁ FEq.≈-refl))
      (FEq.≈-trans FEq.C-assoc (FEq.C-cong FEq.×-β₂ FEq.≈-refl)))

pmap-congᶠ : ∀ {A B U : TY HO} (G : Ty HO 1)
  {f f′ : A F.`× U F.→ᶠ B} →
  f FEq.≈ f′ → F.pmap G f FEq.≈ F.pmap G f′
pmap-congᶠ G f≈ =
  FEq.C-cong (FEq.fmap-cong G f≈) FEq.≈-refl

foldArgs-congᶠ : ∀ {T U} (G : Ty HO 1)
  {p p′ : F.ind G F.`× U F.→ᶠ T} →
  p FEq.≈ p′ → F.foldArgs G p FEq.≈ F.foldArgs G p′
foldArgs-congᶠ G p≈ =
  FEq.`#-cong (pmap-congᶠ G p≈) FEq.≈-refl

pmap-Cᶠ : ∀ {A B D U : TY HO} (G : Ty HO 1)
  {f : B F.→ᶠ D} {g : A F.`× U F.→ᶠ B} →
  F.C (F.fmap G f) (F.pmap G g) FEq.≈ F.pmap G (F.C f g)
pmap-Cᶠ G =
  FEq.≈-trans FEq.C-assoc
    (FEq.C-cong (FEq.≈-sym (FEq.fmap-C G)) FEq.≈-refl)

π₁-con-mapᶠ : ∀ {U} {G : Ty HO 1} →
  F.C F.π₁ (F.map-× (F.con {G = G}) (F.id {T = U}))
  FEq.≈ F.C F.con F.π₁
π₁-con-mapᶠ = FEq.×-β₁

rebuild₀-foldArgs-π₁ᶠ : ∀ {U} (G : Ty HO 1) →
  F.C (rebuild₀ᶠ {U = U} G) (F.foldArgs G F.π₁)
  FEq.≈ F.C F.con F.π₁
rebuild₀-foldArgs-π₁ᶠ G =
  FEq.≈-trans (FEq.≈-sym FEq.C-assoc)
    (FEq.≈-trans
      (FEq.C-cong FEq.≈-refl FEq.×-β₁)
      (FEq.C-cong FEq.≈-refl (FEq.strength-π₁ G)))

π₁-is-F-rebuild₀ᶠ : ∀ {U} (G : Ty HO 1) →
  F.π₁ FEq.≈ F.F {G = G} {T = F.ind G} {U = U} (rebuild₀ᶠ G)
π₁-is-F-rebuild₀ᶠ {U = U} G =
  FEq.F-unique
    (FEq.≈-trans π₁-con-mapᶠ
      (FEq.≈-sym (rebuild₀-foldArgs-π₁ᶠ {U = U} G)))

rebuild-foldArgsᶠ : ∀ {T U} (G : Ty HO 1)
  (r : F.ind G F.`× U F.→ᶠ T F.`× F.ind G) →
  F.C (rebuildᶠ G) (F.foldArgs G r)
  FEq.≈
  F.C (rebuild₀ᶠ G) (F.foldArgs G (F.C F.π₂ r))
rebuild-foldArgsᶠ G r =
  FEq.≈-trans (FEq.≈-sym FEq.C-assoc)
    (FEq.≈-trans
      (FEq.C-cong FEq.≈-refl (FEq.≈-sym FEq.C-assoc))
      (FEq.≈-trans
        (FEq.C-cong FEq.≈-refl
          (FEq.C-cong FEq.≈-refl FEq.×-β₁))
        (FEq.≈-trans
          (FEq.C-cong FEq.≈-refl (pmap-Cᶠ G))
          (FEq.≈-trans
            (FEq.C-cong FEq.≈-refl (FEq.≈-sym FEq.×-β₁))
            FEq.C-assoc))))

second-is-F-rebuild₀ᶠ : ∀ {T U} {G : Ty HO 1}
  (h : (G [ T F.`× F.ind G ]) F.`× U F.→ᶠ T) →
  F.C F.π₂ (F.F (rememberᶠ G h))
  FEq.≈ F.F {G = G} {T = F.ind G} {U = U} (rebuild₀ᶠ G)
second-is-F-rebuild₀ᶠ {G = G} h =
  FEq.F-unique
    (FEq.≈-trans (FEq.≈-sym FEq.C-assoc)
      (FEq.≈-trans
        (FEq.C-cong FEq.≈-refl FEq.F-β)
        (FEq.≈-trans FEq.C-assoc
          (FEq.≈-trans
            (FEq.C-cong FEq.×-β₂ FEq.≈-refl)
            (rebuild-foldArgsᶠ G (F.F (rememberᶠ G h)))))))

remember-secondᶠ : ∀ {T U} {G : Ty HO 1}
  (h : (G [ T F.`× F.ind G ]) F.`× U F.→ᶠ T) →
  F.C F.π₂ (F.F (rememberᶠ G h)) FEq.≈ F.π₁
remember-secondᶠ {G = G} h =
  FEq.≈-trans (second-is-F-rebuild₀ᶠ h)
    (FEq.≈-sym (π₁-is-F-rebuild₀ᶠ G))

remember-ηᶠ : ∀ {T U} {G : Ty HO 1}
  (h : (G [ T F.`× F.ind G ]) F.`× U F.→ᶠ T) →
  F.F (rememberᶠ G h) FEq.≈ F.`# (Pᶠ h) F.π₁
remember-ηᶠ h =
  FEq.≈-trans (FEq.≈-sym FEq.×-η)
    (FEq.`#-cong FEq.≈-refl (remember-secondᶠ h))

foldArgs-rememberᶠ : ∀ {T U} {G : Ty HO 1}
  (h : (G [ T F.`× F.ind G ]) F.`× U F.→ᶠ T) →
  F.foldArgs G (F.F (rememberᶠ G h)) FEq.≈ paraArgsᶠ G (Pᶠ h)
foldArgs-rememberᶠ {G = G} h =
  foldArgs-congᶠ G (remember-ηᶠ h)

Pᶠ-β : ∀ {T U} {G : Ty HO 1}
  {h : (G [ T F.`× F.ind G ]) F.`× U F.→ᶠ T} →
  F.C (Pᶠ {G = G} h) (F.map-× (F.con {G = G}) (F.id {T = U}))
  FEq.≈
  F.C h (paraArgsᶠ G (Pᶠ {G = G} h))
Pᶠ-β {G = G} {h = h} =
  FEq.≈-trans (FEq.≈-sym FEq.C-assoc)
    (FEq.≈-trans
      (FEq.C-cong FEq.≈-refl FEq.F-β)
      (FEq.≈-trans FEq.C-assoc
        (FEq.≈-trans
          (FEq.C-cong FEq.×-β₁ FEq.≈-refl)
          (FEq.C-cong FEq.≈-refl (foldArgs-rememberᶠ h)))))

rebuild-paraArgsᶠ : ∀ {T U} (G : Ty HO 1)
  (p : F.ind G F.`× U F.→ᶠ T) →
  F.C (rebuildᶠ G) (paraArgsᶠ G p) FEq.≈ F.C F.con F.π₁
rebuild-paraArgsᶠ G p =
  FEq.≈-trans (rebuild-foldArgsᶠ G (F.`# p F.π₁))
    (FEq.≈-trans
      (FEq.C-cong FEq.≈-refl
        (foldArgs-congᶠ G FEq.×-β₂))
      (rebuild₀-foldArgs-π₁ᶠ G))

Pᶠ-unique : ∀ {T U} {G : Ty HO 1}
  {h : (G [ T F.`× F.ind G ]) F.`× U F.→ᶠ T}
  {p : F.ind G F.`× U F.→ᶠ T} →
  F.C p (F.map-× (F.con {G = G}) (F.id {T = U}))
  FEq.≈ F.C h (paraArgsᶠ G p) →
  p FEq.≈ Pᶠ {G = G} h
Pᶠ-unique {G = G} {h = h} {p = p} premise =
  FEq.≈-trans (FEq.≈-sym FEq.×-β₁)
    (FEq.C-cong FEq.≈-refl
      (FEq.F-unique
        (FEq.≈-trans C-#ᶠ
          (FEq.≈-trans
            (FEq.`#-cong premise
              (FEq.≈-trans π₁-con-mapᶠ
                (FEq.≈-sym (rebuild-paraArgsᶠ G p))))
            (FEq.≈-sym C-#ᶠ)))))

toF-preserves : ∀ {T U} {f g : T P.→ᴾ U} →
  f PEq.≈ g → toF f FEq.≈ toF g
toF-preserves PEq.≈-refl = FEq.≈-refl
toF-preserves (PEq.≈-sym p) = FEq.≈-sym (toF-preserves p)
toF-preserves (PEq.≈-trans p q) =
  FEq.≈-trans (toF-preserves p) (toF-preserves q)
toF-preserves (PEq.C-cong p q) =
  FEq.C-cong (toF-preserves p) (toF-preserves q)
toF-preserves (PEq.`#-cong p q) =
  FEq.`#-cong (toF-preserves p) (toF-preserves q)
toF-preserves (PEq.`case-cong p q) =
  FEq.`case-cong (toF-preserves p) (toF-preserves q)
toF-preserves (PEq.lam-cong p) =
  FEq.lam-cong (toF-preserves p)
toF-preserves (PEq.fmap-cong G p) =
  FEq.fmap-cong G (toF-preserves p)
toF-preserves (PEq.P-cong {H = H} p) =
  FEq.C-cong FEq.≈-refl
    (FEq.F-cong (FEq.`#-cong (toF-preserves p) FEq.≈-refl))
toF-preserves PEq.C-idˡ = FEq.C-idˡ
toF-preserves PEq.C-idʳ = FEq.C-idʳ
toF-preserves PEq.C-assoc = FEq.C-assoc
toF-preserves (PEq.fmap-id G) = FEq.fmap-id G
toF-preserves (PEq.fmap-C G) = FEq.fmap-C G
toF-preserves (PEq.fmap-βᶜ S {f = f})
  rewrite toF-fmapᶜ S f = FEq.fmap-βᶜ S
toF-preserves (PEq.strength-naturalˡ G) = FEq.strength-naturalˡ G
toF-preserves (PEq.strength-naturalʳ G) = FEq.strength-naturalʳ G
toF-preserves (PEq.strength-π₁ G) = FEq.strength-π₁ G
toF-preserves (PEq.strength-βᶜ {A = A} {B = B} S)
  rewrite toF-strengthᶜ {T = A} {U = B} S = FEq.strength-βᶜ S
toF-preserves PEq.𝟙-unique = FEq.𝟙-unique
toF-preserves PEq.𝟘-unique = FEq.𝟘-unique
toF-preserves PEq.×-β₁ = FEq.×-β₁
toF-preserves PEq.×-β₂ = FEq.×-β₂
toF-preserves PEq.×-η = FEq.×-η
toF-preserves PEq.+-β₁ = FEq.+-β₁
toF-preserves PEq.+-β₂ = FEq.+-β₂
toF-preserves PEq.+-η = FEq.+-η
toF-preserves PEq.⇒-β = FEq.⇒-β
toF-preserves PEq.⇒-η = FEq.⇒-η
toF-preserves (PEq.P-β {H = H} {h = h}) =
  Pᶠ-β {G = H} {h = toF h}
toF-preserves (PEq.P-unique p) =
  Pᶠ-unique (toF-preserves p)

----------------------------------------------------------------------
-- Round trips up to the respective equational theories
----------------------------------------------------------------------

toP-toF : ∀ {T U} (f : T P.→ᴾ U) → toP (toF f) PEq.≈ f
toP-toF P.id = PEq.≈-refl
toP-toF (P.C f g) = PEq.C-cong (toP-toF f) (toP-toF g)
toP-toF P.`⊤ = PEq.≈-refl
toP-toF P.`⊥ = PEq.≈-refl
toP-toF (P.`# f g) = PEq.`#-cong (toP-toF f) (toP-toF g)
toP-toF P.π₁ = PEq.≈-refl
toP-toF P.π₂ = PEq.≈-refl
toP-toF P.ι₁ = PEq.≈-refl
toP-toF P.ι₂ = PEq.≈-refl
toP-toF (P.`case f g) = PEq.`case-cong (toP-toF f) (toP-toF g)
toP-toF (P.lam f) = PEq.lam-cong (toP-toF f)
toP-toF P.apply = PEq.≈-refl
toP-toF (P.fmap G f) = PEq.fmap-cong G (toP-toF f)
toP-toF (P.strength G) = PEq.≈-refl
toP-toF P.con = PEq.≈-refl
toP-toF {T = ind G `× U} {U = T} (P.P h) =
  PEq.P-unique
    (PEq.≈-trans
      (toP-preserves (Pᶠ-β {G = G} {h = toF h}))
      (PEq.C-cong (toP-toF h) PEq.≈-refl))

toF-toP : ∀ {T U} (f : T F.→ᶠ U) → toF (toP f) FEq.≈ f
toF-toP F.id = FEq.≈-refl
toF-toP (F.C f g) = FEq.C-cong (toF-toP f) (toF-toP g)
toF-toP F.`⊤ = FEq.≈-refl
toF-toP F.`⊥ = FEq.≈-refl
toF-toP (F.`# f g) = FEq.`#-cong (toF-toP f) (toF-toP g)
toF-toP F.π₁ = FEq.≈-refl
toF-toP F.π₂ = FEq.≈-refl
toF-toP F.ι₁ = FEq.≈-refl
toF-toP F.ι₂ = FEq.≈-refl
toF-toP (F.`case f g) = FEq.`case-cong (toF-toP f) (toF-toP g)
toF-toP (F.lam f) = FEq.lam-cong (toF-toP f)
toF-toP F.apply = FEq.≈-refl
toF-toP (F.fmap G f) = FEq.fmap-cong G (toF-toP f)
toF-toP (F.strength G) = FEq.≈-refl
toF-toP F.con = FEq.≈-refl
toF-toP (F.F {G = G} h) =
  FEq.F-unique
    (FEq.≈-trans
      (toF-preserves (Fᴾ-β {G = G} {h = toP h}))
      (FEq.C-cong (toF-toP h) FEq.≈-refl))
