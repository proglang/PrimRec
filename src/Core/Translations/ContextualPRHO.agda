{-# OPTIONS --safe #-}

module Core.Translations.ContextualPRHO where

import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl; cong; cong₂)

import Core.PRHO as PF
import Core.Equations.PRHO as PFEq
import Core.Contextual.PRHO as Ctx
import Core.Contextual.Equations.PRHO as CtxEq

----------------------------------------------------------------------
-- Translations
----------------------------------------------------------------------

compile : ∀ {Γ A} → Γ Ctx.⊢ A → Γ PF.→ᴾ A
compile Ctx.var = PF.id
compile (Ctx.cut t u) = PF.C (compile t) (compile u)
compile Ctx.unit = PF.`⊤
compile Ctx.abort = PF.`⊥
compile (Ctx.pair t u) = PF.`# (compile t) (compile u)
compile Ctx.fst = PF.π₁
compile Ctx.snd = PF.π₂
compile Ctx.inl = PF.ι₁
compile Ctx.inr = PF.ι₂
compile (Ctx.cases t u) = PF.`case (compile t) (compile u)
compile (Ctx.curry t) = PF.lam (compile t)
compile Ctx.eval = PF.apply
compile (Ctx.fmap G t) = PF.fmap G (compile t)
compile (Ctx.strength G) = PF.strength G
compile Ctx.con = PF.con
compile (Ctx.prec h) = PF.P (compile h)

reify : ∀ {Γ A} → Γ PF.→ᴾ A → Γ Ctx.⊢ A
reify PF.id = Ctx.var
reify (PF.C f g) = Ctx.cut (reify f) (reify g)
reify PF.`⊤ = Ctx.unit
reify PF.`⊥ = Ctx.abort
reify (PF.`# f g) = Ctx.pair (reify f) (reify g)
reify PF.π₁ = Ctx.fst
reify PF.π₂ = Ctx.snd
reify PF.ι₁ = Ctx.inl
reify PF.ι₂ = Ctx.inr
reify (PF.`case f g) = Ctx.cases (reify f) (reify g)
reify (PF.lam f) = Ctx.curry (reify f)
reify PF.apply = Ctx.eval
reify (PF.fmap G f) = Ctx.fmap G (reify f)
reify (PF.strength G) = Ctx.strength G
reify PF.con = Ctx.con
reify (PF.P h) = Ctx.prec (reify h)

----------------------------------------------------------------------
-- The translations are mutually inverse on raw syntax.
----------------------------------------------------------------------

compile-reify : ∀ {Γ A} (f : Γ PF.→ᴾ A) → compile (reify f) ≡ f
compile-reify PF.id = refl
compile-reify (PF.C f g) = cong₂ PF.C (compile-reify f) (compile-reify g)
compile-reify PF.`⊤ = refl
compile-reify PF.`⊥ = refl
compile-reify (PF.`# f g) = cong₂ PF.`# (compile-reify f) (compile-reify g)
compile-reify PF.π₁ = refl
compile-reify PF.π₂ = refl
compile-reify PF.ι₁ = refl
compile-reify PF.ι₂ = refl
compile-reify (PF.`case f g) = cong₂ PF.`case (compile-reify f) (compile-reify g)
compile-reify (PF.lam f) = cong PF.lam (compile-reify f)
compile-reify PF.apply = refl
compile-reify (PF.fmap G f) = cong (PF.fmap G) (compile-reify f)
compile-reify (PF.strength G) = refl
compile-reify PF.con = refl
compile-reify (PF.P h) = cong PF.P (compile-reify h)

reify-compile : ∀ {Γ A} (t : Γ Ctx.⊢ A) → reify (compile t) ≡ t
reify-compile Ctx.var = refl
reify-compile (Ctx.cut t u) = cong₂ Ctx.cut (reify-compile t) (reify-compile u)
reify-compile Ctx.unit = refl
reify-compile Ctx.abort = refl
reify-compile (Ctx.pair t u) = cong₂ Ctx.pair (reify-compile t) (reify-compile u)
reify-compile Ctx.fst = refl
reify-compile Ctx.snd = refl
reify-compile Ctx.inl = refl
reify-compile Ctx.inr = refl
reify-compile (Ctx.cases t u) = cong₂ Ctx.cases (reify-compile t) (reify-compile u)
reify-compile (Ctx.curry t) = cong Ctx.curry (reify-compile t)
reify-compile Ctx.eval = refl
reify-compile (Ctx.fmap G t) = cong (Ctx.fmap G) (reify-compile t)
reify-compile (Ctx.strength G) = refl
reify-compile Ctx.con = refl
reify-compile (Ctx.prec h) = cong Ctx.prec (reify-compile h)

compile-reify≈ : ∀ {Γ A} (f : Γ PF.→ᴾ A) → compile (reify f) PFEq.≈ f
compile-reify≈ f rewrite compile-reify f = PFEq.≈-refl

reify-compile≈ : ∀ {Γ A} (t : Γ Ctx.⊢ A) → reify (compile t) CtxEq.≈ t
reify-compile≈ t rewrite reify-compile t = CtxEq.≈-refl

compile-fmapᶜ : ∀ {A B G} (S : Ctx.StructuralFunctor G)
  (t : A Ctx.⊢ B) →
  compile (Ctx.fmapᶜ S t) ≡ PF.fmapᶜ S (compile t)
compile-fmapᶜ Ctx.sf-𝟘 t = refl
compile-fmapᶜ Ctx.sf-𝟙 t = refl
compile-fmapᶜ Ctx.sf-var t = refl
compile-fmapᶜ (Ctx.sf-× S R) t
  rewrite compile-fmapᶜ S t | compile-fmapᶜ R t = refl
compile-fmapᶜ (Ctx.sf-+ S R) t
  rewrite compile-fmapᶜ S t | compile-fmapᶜ R t = refl
compile-fmapᶜ (Ctx.sf-⇒ A S) t
  rewrite compile-fmapᶜ S t = refl

compile-strengthᶜ : ∀ {A B G} (S : Ctx.StructuralFunctor G) →
  compile (Ctx.strengthᶜ {A = A} {B = B} S) ≡ PF.strengthᶜ S
compile-strengthᶜ Ctx.sf-𝟘 = refl
compile-strengthᶜ Ctx.sf-𝟙 = refl
compile-strengthᶜ Ctx.sf-var = refl
compile-strengthᶜ {A = A} {B = B} (Ctx.sf-× S R)
  rewrite compile-strengthᶜ {A = A} {B = B} S
        | compile-strengthᶜ {A = A} {B = B} R = refl
compile-strengthᶜ {A = A} {B = B} (Ctx.sf-+ S R)
  rewrite compile-strengthᶜ {A = A} {B = B} S
        | compile-strengthᶜ {A = A} {B = B} R = refl
compile-strengthᶜ {A = A} {B = B} (Ctx.sf-⇒ C S)
  rewrite compile-strengthᶜ {A = A} {B = B} S = refl

reify-fmapᶜ : ∀ {A B G} (S : Ctx.StructuralFunctor G)
  (f : A PF.→ᴾ B) →
  reify (PF.fmapᶜ S f) ≡ Ctx.fmapᶜ S (reify f)
reify-fmapᶜ Ctx.sf-𝟘 f = refl
reify-fmapᶜ Ctx.sf-𝟙 f = refl
reify-fmapᶜ Ctx.sf-var f = refl
reify-fmapᶜ (Ctx.sf-× S R) f
  rewrite reify-fmapᶜ S f | reify-fmapᶜ R f = refl
reify-fmapᶜ (Ctx.sf-+ S R) f
  rewrite reify-fmapᶜ S f | reify-fmapᶜ R f = refl
reify-fmapᶜ (Ctx.sf-⇒ A S) f
  rewrite reify-fmapᶜ S f = refl

reify-strengthᶜ : ∀ {A B G} (S : Ctx.StructuralFunctor G) →
  reify (PF.strengthᶜ {T = A} {U = B} S) ≡ Ctx.strengthᶜ S
reify-strengthᶜ Ctx.sf-𝟘 = refl
reify-strengthᶜ Ctx.sf-𝟙 = refl
reify-strengthᶜ Ctx.sf-var = refl
reify-strengthᶜ {A = A} {B = B} (Ctx.sf-× S R)
  rewrite reify-strengthᶜ {A = A} {B = B} S
        | reify-strengthᶜ {A = A} {B = B} R = refl
reify-strengthᶜ {A = A} {B = B} (Ctx.sf-+ S R)
  rewrite reify-strengthᶜ {A = A} {B = B} S
        | reify-strengthᶜ {A = A} {B = B} R = refl
reify-strengthᶜ {A = A} {B = B} (Ctx.sf-⇒ C S)
  rewrite reify-strengthᶜ {A = A} {B = B} S = refl

----------------------------------------------------------------------
-- Both translations preserve the independently generated equations.
----------------------------------------------------------------------

compile-sound : ∀ {Γ A} {t u : Γ Ctx.⊢ A} → t CtxEq.≈ u → compile t PFEq.≈ compile u
compile-sound CtxEq.≈-refl = PFEq.≈-refl
compile-sound (CtxEq.≈-sym p) = PFEq.≈-sym (compile-sound p)
compile-sound (CtxEq.≈-trans p q) = PFEq.≈-trans (compile-sound p) (compile-sound q)
compile-sound (CtxEq.cut-cong p q) = PFEq.C-cong (compile-sound p) (compile-sound q)
compile-sound (CtxEq.pair-cong p q) = PFEq.`#-cong (compile-sound p) (compile-sound q)
compile-sound (CtxEq.cases-cong p q) = PFEq.`case-cong (compile-sound p) (compile-sound q)
compile-sound (CtxEq.curry-cong p) = PFEq.lam-cong (compile-sound p)
compile-sound (CtxEq.fmap-cong G p) = PFEq.fmap-cong G (compile-sound p)
compile-sound (CtxEq.prec-cong p) = PFEq.P-cong (compile-sound p)
compile-sound CtxEq.cut-varˡ = PFEq.C-idˡ
compile-sound CtxEq.cut-varʳ = PFEq.C-idʳ
compile-sound CtxEq.cut-assoc = PFEq.C-assoc
compile-sound (CtxEq.fmap-var G) = PFEq.fmap-id G
compile-sound (CtxEq.fmap-cut G) = PFEq.fmap-C G
compile-sound (CtxEq.fmap-βᶜ S {t = t})
  rewrite compile-fmapᶜ S t = PFEq.fmap-βᶜ S
compile-sound (CtxEq.strength-naturalˡ G) = PFEq.strength-naturalˡ G
compile-sound (CtxEq.strength-naturalʳ G) = PFEq.strength-naturalʳ G
compile-sound (CtxEq.strength-π₁ G) = PFEq.strength-π₁ G
compile-sound (CtxEq.strength-βᶜ {A = A} {B = B} S)
  rewrite compile-strengthᶜ {A = A} {B = B} S = PFEq.strength-βᶜ S
compile-sound CtxEq.𝟙-unique = PFEq.𝟙-unique
compile-sound CtxEq.𝟘-unique = PFEq.𝟘-unique
compile-sound CtxEq.×-β₁ = PFEq.×-β₁
compile-sound CtxEq.×-β₂ = PFEq.×-β₂
compile-sound CtxEq.×-η = PFEq.×-η
compile-sound CtxEq.+-β₁ = PFEq.+-β₁
compile-sound CtxEq.+-β₂ = PFEq.+-β₂
compile-sound CtxEq.+-η = PFEq.+-η
compile-sound CtxEq.⇒-β = PFEq.⇒-β
compile-sound CtxEq.⇒-η = PFEq.⇒-η
compile-sound CtxEq.prec-β = PFEq.P-β
compile-sound (CtxEq.prec-unique p) = PFEq.P-unique (compile-sound p)

reify-sound : ∀ {Γ A} {f g : Γ PF.→ᴾ A} → f PFEq.≈ g → reify f CtxEq.≈ reify g
reify-sound PFEq.≈-refl = CtxEq.≈-refl
reify-sound (PFEq.≈-sym p) = CtxEq.≈-sym (reify-sound p)
reify-sound (PFEq.≈-trans p q) = CtxEq.≈-trans (reify-sound p) (reify-sound q)
reify-sound (PFEq.C-cong p q) = CtxEq.cut-cong (reify-sound p) (reify-sound q)
reify-sound (PFEq.`#-cong p q) = CtxEq.pair-cong (reify-sound p) (reify-sound q)
reify-sound (PFEq.`case-cong p q) = CtxEq.cases-cong (reify-sound p) (reify-sound q)
reify-sound (PFEq.lam-cong p) = CtxEq.curry-cong (reify-sound p)
reify-sound (PFEq.fmap-cong G p) = CtxEq.fmap-cong G (reify-sound p)
reify-sound (PFEq.P-cong p) = CtxEq.prec-cong (reify-sound p)
reify-sound PFEq.C-idˡ = CtxEq.cut-varˡ
reify-sound PFEq.C-idʳ = CtxEq.cut-varʳ
reify-sound PFEq.C-assoc = CtxEq.cut-assoc
reify-sound (PFEq.fmap-id G) = CtxEq.fmap-var G
reify-sound (PFEq.fmap-C G) = CtxEq.fmap-cut G
reify-sound (PFEq.fmap-βᶜ S {f = f})
  rewrite reify-fmapᶜ S f = CtxEq.fmap-βᶜ S
reify-sound (PFEq.strength-naturalˡ G) = CtxEq.strength-naturalˡ G
reify-sound (PFEq.strength-naturalʳ G) = CtxEq.strength-naturalʳ G
reify-sound (PFEq.strength-π₁ G) = CtxEq.strength-π₁ G
reify-sound (PFEq.strength-βᶜ {A = A} {B = B} S)
  rewrite reify-strengthᶜ {A = A} {B = B} S = CtxEq.strength-βᶜ S
reify-sound PFEq.𝟙-unique = CtxEq.𝟙-unique
reify-sound PFEq.𝟘-unique = CtxEq.𝟘-unique
reify-sound PFEq.×-β₁ = CtxEq.×-β₁
reify-sound PFEq.×-β₂ = CtxEq.×-β₂
reify-sound PFEq.×-η = CtxEq.×-η
reify-sound PFEq.+-β₁ = CtxEq.+-β₁
reify-sound PFEq.+-β₂ = CtxEq.+-β₂
reify-sound PFEq.+-η = CtxEq.+-η
reify-sound PFEq.⇒-β = CtxEq.⇒-β
reify-sound PFEq.⇒-η = CtxEq.⇒-η
reify-sound PFEq.P-β = CtxEq.prec-β
reify-sound (PFEq.P-unique p) = CtxEq.prec-unique (reify-sound p)
