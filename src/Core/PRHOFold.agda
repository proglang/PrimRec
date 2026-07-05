{-# OPTIONS --safe #-}

module Core.PRHOFold where

open import Core.Types public

infix 6 _→ᶠ_

variable
  W : TY HO

----------------------------------------------------------------------
-- Point-free higher-order syntax with primitive catamorphism
----------------------------------------------------------------------

data _→ᶠ_ : TY HO → TY HO → Set where
  -- category
  id : T →ᶠ T
  C  : U →ᶠ V → T →ᶠ U → T →ᶠ V

  -- initial and terminal objects
  `⊤ : T →ᶠ `𝟙
  `⊥ : `𝟘 →ᶠ T

  -- products
  `# : T →ᶠ U → T →ᶠ V → T →ᶠ U `× V
  π₁ : U `× V →ᶠ U
  π₂ : U `× V →ᶠ V

  -- sums
  ι₁ : U →ᶠ U `+ V
  ι₂ : V →ᶠ U `+ V
  `case : U →ᶠ T → V →ᶠ T → U `+ V →ᶠ T

  -- exponentials
  lam   : U `× V →ᶠ T → U →ᶠ V `⇒ T
  apply : (T `⇒ U) `× T →ᶠ U

  -- functorial action and its right strength
  fmap : (G : Ty HO 1) → T →ᶠ U → G [ T ] →ᶠ G [ U ]
  strength : (G : Ty HO 1) → (G [ T ]) `× U →ᶠ G [ T `× U ]

  -- inductive types and catamorphism
  con : G [ ind G ] →ᶠ ind G
  F : (G [ T ]) `× U →ᶠ T
    → ind G `× U →ᶠ T

map-× : U →ᶠ T → V →ᶠ W → U `× V →ᶠ T `× W
map-× f g = `# (C f π₁) (C g π₂)

fmapᶜ : ∀ {T U G} → StructuralFunctor G → T →ᶠ U → G [ T ] →ᶠ G [ U ]
fmapᶜ sf-𝟘 f = id
fmapᶜ sf-𝟙 f = id
fmapᶜ sf-var f = f
fmapᶜ (sf-× S R) f = map-× (fmapᶜ S f) (fmapᶜ R f)
fmapᶜ (sf-+ S R) f =
  `case (C ι₁ (fmapᶜ S f)) (C ι₂ (fmapᶜ R f))
fmapᶜ (sf-⇒ A S) f = lam (C (fmapᶜ S f) apply)

pmap : (G : Ty HO 1) → T `× U →ᶠ V
  → (G [ T ]) `× U →ᶠ G [ V ]
pmap G f = C (fmap G f) (strength G)

foldArgs : (G : Ty HO 1) → ind G `× U →ᶠ T
  → (G [ ind G ]) `× U →ᶠ (G [ T ]) `× U
foldArgs G f = `# (pmap G f) π₂

theta : U →ᶠ V `⇒ T → U `× V →ᶠ T
theta f = C apply (map-× f id)

dist-+-× : (U `+ V) `× T →ᶠ (U `× T) `+ (V `× T)
dist-+-× = theta (`case (lam ι₁) (lam ι₂))

undist-+-× : (U `× T) `+ (V `× T) →ᶠ (U `+ V) `× T
undist-+-× = `case (`# (C ι₁ π₁) π₂) (`# (C ι₂ π₁) π₂)

strengthᶜ : ∀ {T U G} → StructuralFunctor G →
  (G [ T ]) `× U →ᶠ G [ T `× U ]
strengthᶜ sf-𝟘 = π₁
strengthᶜ sf-𝟙 = π₁
strengthᶜ sf-var = id
strengthᶜ (sf-× S R) =
  `#
    (C (strengthᶜ S) (`# (C π₁ π₁) π₂))
    (C (strengthᶜ R) (`# (C π₂ π₁) π₂))
strengthᶜ (sf-+ S R) =
  C (`case (C ι₁ (strengthᶜ S)) (C ι₂ (strengthᶜ R))) dist-+-×
strengthᶜ (sf-⇒ A S) =
  lam
    (C (strengthᶜ S)
      (`# (C apply (`# (C π₁ π₁) π₂))
          (C π₂ π₁)))
