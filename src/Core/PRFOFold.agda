{-# OPTIONS --safe #-}

module Core.PRFOFold where

open import Core.Types public

infix 6 _→ᶠ_

variable
  T U V W : TY FO
  G : Ty FO 1

----------------------------------------------------------------------
-- Point-free first-order syntax with primitive catamorphism
----------------------------------------------------------------------

data _→ᶠ_ : TY FO → TY FO → Set where
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

  -- distributivity
  dist-+-× : (U `+ V) `× T →ᶠ (U `× T) `+ (V `× T)

  -- functorial action and its right strength
  fmap : (G : Ty FO 1) → (T →ᶠ U) → (G [ T ] →ᶠ G [ U ])
  strength : (G : Ty FO 1) → (G [ T ]) `× U →ᶠ G [ T `× U ]

  --! CorePRFOFoldPrimitive {
  -- inductive types and catamorphism
  roll      : G [ ind G ] →ᶠ ind G
  F         : (G [ T ]) `× U →ᶠ T
    → ind G `× U →ᶠ T
  --! }

map-× : U →ᶠ T → V →ᶠ W → U `× V →ᶠ T `× W
map-× f g = `# (C f π₁) (C g π₂)

pmap : (G : Ty FO 1) → (T `× U →ᶠ V)
  → ((G [ T ]) `× U →ᶠ G [ V ])
pmap G f = C (fmap G f) (strength G)

foldArgs : (G : Ty FO 1) → (ind G `× U →ᶠ T)
  → ((G [ ind G ]) `× U →ᶠ (G [ T ]) `× U)
foldArgs G f = `# (pmap G f) π₂

undist-+-× : (U `× T) `+ (V `× T) →ᶠ (U `+ V) `× T
undist-+-× = `case (`# (C ι₁ π₁) π₂) (`# (C ι₂ π₁) π₂)
