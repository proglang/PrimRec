{-# OPTIONS --safe #-}

module Core.PRFOCatamorphism where

open import Core.Types public

infix 6 _→ᶜ_

variable
  W : TY FO

----------------------------------------------------------------------
-- Point-free first-order syntax with primitive catamorphism
----------------------------------------------------------------------

data _→ᶜ_ : TY FO → TY FO → Set where
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

  -- distributivity
  dist-+-× : (U `+ V) `× T →ᶜ (U `× T) `+ (V `× T)

  -- functorial action and its right strength
  fmap      : (G : Ty FO 1) → (T →ᶜ U) → (G [ T ] →ᶜ G [ U ])
  strength  : (G : Ty FO 1) → (G [ T ]) `× U →ᶜ G [ T `× U ]

  --! CorePRFOCatamorphismPrimitive {
  -- inductive types and catamorphism
  con       : G [ ind G ] →ᶜ ind G
  Ct         : (G [ T ]) `× U →ᶜ T → ind G `× U →ᶜ T
  --! }

map-× : U →ᶜ T → V →ᶜ W → U `× V →ᶜ T `× W
map-× f g = `# (C f π₁) (C g π₂)

pmap : (G : Ty FO 1) → (T `× U →ᶜ V)
  → ((G [ T ]) `× U →ᶜ G [ V ])
pmap G f = C (fmap G f) (strength G)

catamorphismArgs : (G : Ty FO 1) → (ind G `× U →ᶜ T)
  → ((G [ ind G ]) `× U →ᶜ (G [ T ]) `× U)
catamorphismArgs G f = `# (pmap G f) π₂

undist-+-× : (U `× T) `+ (V `× T) →ᶜ (U `+ V) `× T
undist-+-× = `case (`# (C ι₁ π₁) π₂) (`# (C ι₂ π₁) π₂)
