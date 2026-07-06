{-# OPTIONS --safe #-}

module Core.PRHOCatamorphism where

open import Core.Types public

infix 6 _→ᶜ_

variable
  W : TY HO

----------------------------------------------------------------------
-- Point-free higher-order syntax with primitive catamorphism
----------------------------------------------------------------------

data _→ᶜ_ : TY HO → TY HO → Set where
  -- category
  id : T →ᶜ T
  C  : U →ᶜ V → T →ᶜ U → T →ᶜ V

  -- initial and terminal objects
  `⊤ : T →ᶜ `𝟙
  `⊥ : `𝟘 →ᶜ T

  -- products
  `# : T →ᶜ U → T →ᶜ V → T →ᶜ U `× V
  π₁ : U `× V →ᶜ U
  π₂ : U `× V →ᶜ V

  -- sums
  ι₁ : U →ᶜ U `+ V
  ι₂ : V →ᶜ U `+ V
  `case : U →ᶜ T → V →ᶜ T → U `+ V →ᶜ T

  -- exponentials
  lam   : U `× V →ᶜ T → U →ᶜ V `⇒ T
  apply : (T `⇒ U) `× T →ᶜ U

  -- functorial action and its right strength
  fmap : (G : Ty HO 1) → T →ᶜ U → G [ T ] →ᶜ G [ U ]
  strength : (G : Ty HO 1) → (G [ T ]) `× U →ᶜ G [ T `× U ]

  -- inductive types and catamorphism
  con : G [ ind G ] →ᶜ ind G
  Ct : (G [ T ]) `× U →ᶜ T
    → ind G `× U →ᶜ T

map-× : U →ᶜ T → V →ᶜ W → U `× V →ᶜ T `× W
map-× f g = `# (C f π₁) (C g π₂)

fmapᶜ : ∀ {T U G} → StructuralFunctor G → T →ᶜ U → G [ T ] →ᶜ G [ U ]
fmapᶜ sf-𝟘 f = id
fmapᶜ sf-𝟙 f = id
fmapᶜ sf-var f = f
fmapᶜ (sf-× S R) f = map-× (fmapᶜ S f) (fmapᶜ R f)
fmapᶜ (sf-+ S R) f =
  `case (C ι₁ (fmapᶜ S f)) (C ι₂ (fmapᶜ R f))
fmapᶜ (sf-⇒ A S) f = lam (C (fmapᶜ S f) apply)

pmap : (G : Ty HO 1) → T `× U →ᶜ V
  → (G [ T ]) `× U →ᶜ G [ V ]
pmap G f = C (fmap G f) (strength G)

catamorphismArgs : (G : Ty HO 1) → ind G `× U →ᶜ T
  → (G [ ind G ]) `× U →ᶜ (G [ T ]) `× U
catamorphismArgs G f = `# (pmap G f) π₂

theta : U →ᶜ V `⇒ T → U `× V →ᶜ T
theta f = C apply (map-× f id)

dist-+-× : (U `+ V) `× T →ᶜ (U `× T) `+ (V `× T)
dist-+-× = theta (`case (lam ι₁) (lam ι₂))

undist-+-× : (U `× T) `+ (V `× T) →ᶜ (U `+ V) `× T
undist-+-× = `case (`# (C ι₁ π₁) π₂) (`# (C ι₂ π₁) π₂)

strengthᶜ : ∀ {T U G} → StructuralFunctor G →
  (G [ T ]) `× U →ᶜ G [ T `× U ]
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
