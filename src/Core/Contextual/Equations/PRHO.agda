{-# OPTIONS --safe #-}

module Core.Contextual.Equations.PRHO where

open import Core.Contextual.PRHO public

infix 4 _≈_

data _≈_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set where
  ≈-refl  : ∀ {Γ A} {t : Γ ⊢ A} → t ≈ t
  ≈-sym   : ∀ {Γ A} {t u : Γ ⊢ A} → t ≈ u → u ≈ t
  ≈-trans : ∀ {Γ A} {t u v : Γ ⊢ A} → t ≈ u → u ≈ v → t ≈ v

  cut-cong : ∀ {Γ A B} {t t′ : A ⊢ B} {u u′ : Γ ⊢ A}
    → t ≈ t′ → u ≈ u′ → cut t u ≈ cut t′ u′
  pair-cong : ∀ {Γ A B} {t t′ : Γ ⊢ A} {u u′ : Γ ⊢ B}
    → t ≈ t′ → u ≈ u′ → pair t u ≈ pair t′ u′
  cases-cong : ∀ {A B C} {t t′ : A ⊢ C} {u u′ : B ⊢ C}
    → t ≈ t′ → u ≈ u′ → cases t u ≈ cases t′ u′
  curry-cong : ∀ {A B C} {t t′ : A `× B ⊢ C}
    → t ≈ t′ → curry t ≈ curry t′
  fmap-cong : ∀ {A B} (G : Ty HO 1) {t t′ : A ⊢ B}
    → t ≈ t′ → fmap G t ≈ fmap G t′
  prec-cong : ∀ {A B} {G : Ty HO 1}
    {h h′ : (G [ A `× ind G ]) `× B ⊢ A}
    → h ≈ h′
    → prec {G = G} {A = A} {B = B} h ≈ prec {G = G} {A = A} {B = B} h′

  cut-varˡ : ∀ {Γ A} {t : Γ ⊢ A} → cut var t ≈ t
  cut-varʳ : ∀ {Γ A} {t : Γ ⊢ A} → cut t var ≈ t
  cut-assoc : ∀ {Γ A B C} {t : B ⊢ C} {u : A ⊢ B} {v : Γ ⊢ A}
    → cut t (cut u v) ≈ cut (cut t u) v

  fmap-var : ∀ {A} (G : Ty HO 1) → fmap G (var { Γ = A }) ≈ var
  fmap-cut : ∀ {A B C} (G : Ty HO 1) {t : B ⊢ C} {u : A ⊢ B}
    → fmap G (cut t u) ≈ cut (fmap G t) (fmap G u)
  fmap-βᶜ : ∀ {A B} {G : Ty HO 1}
    (S : StructuralFunctor G) {t : A ⊢ B}
    → fmap G t ≈ fmapᶜ S t

  strength-naturalˡ : ∀ {A B C} (G : Ty HO 1) {t : A ⊢ B}
    → cut (fmap G (map-× t (var { Γ = C }))) (strength {A = A} {B = C} G)
      ≈ cut (strength {A = B} {B = C} G) (map-× (fmap G t) var)
  strength-naturalʳ : ∀ {A B C} (G : Ty HO 1) {t : B ⊢ C}
    → cut (fmap G (map-× (var { Γ = A }) t)) (strength {A = A} {B = B} G)
      ≈ cut (strength {A = A} {B = C} G) (map-× var t)
  strength-π₁ : ∀ {A B} (G : Ty HO 1)
    → cut (fmap G (fst {A = A} {B = B})) (strength {A = A} {B = B} G)
      ≈ fst
  strength-βᶜ : ∀ {A B} {G : Ty HO 1}
    (S : StructuralFunctor G)
    → strength {A = A} {B = B} G ≈ strengthᶜ S

  𝟙-unique : ∀ {Γ} {t : Γ ⊢ `𝟙} → t ≈ unit
  𝟘-unique : ∀ {A} {t : `𝟘 ⊢ A} → t ≈ abort

  ×-β₁ : ∀ {Γ A B} {t : Γ ⊢ A} {u : Γ ⊢ B} → cut fst (pair t u) ≈ t
  ×-β₂ : ∀ {Γ A B} {t : Γ ⊢ A} {u : Γ ⊢ B} → cut snd (pair t u) ≈ u
  ×-η : ∀ {Γ A B} {t : Γ ⊢ A `× B} → pair (cut fst t) (cut snd t) ≈ t

  +-β₁ : ∀ {A B C} {t : A ⊢ C} {u : B ⊢ C} → cut (cases t u) inl ≈ t
  +-β₂ : ∀ {A B C} {t : A ⊢ C} {u : B ⊢ C} → cut (cases t u) inr ≈ u
  +-η : ∀ {A B C} {t : A `+ B ⊢ C} → cases (cut t inl) (cut t inr) ≈ t

  ⇒-β : ∀ {A B C} {t : A `× B ⊢ C} → uncurry (curry t) ≈ t
  ⇒-η : ∀ {A B C} {t : A ⊢ B `⇒ C} → curry (uncurry t) ≈ t

  prec-β : ∀ {A B} {G : Ty HO 1}
    {h : (G [ A `× ind G ]) `× B ⊢ A}
    → cut (prec {G = G} {A = A} {B = B} h) (map-× con var)
      ≈ cut h (paraArgs G (prec {G = G} {A = A} {B = B} h))

  prec-unique : ∀ {A B} {G : Ty HO 1}
    {h : (G [ A `× ind G ]) `× B ⊢ A}
    {p : ind G `× B ⊢ A}
    → cut p (map-× con var) ≈ cut h (paraArgs G p)
    → p ≈ prec {G = G} {A = A} {B = B} h
