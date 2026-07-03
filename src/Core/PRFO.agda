{-# OPTIONS --safe #-}

module Core.PRFO where

open import Core.Types public

infix 6 _→ᴾ_

variable
  T U V W : TY FO
  G : Ty FO 1

----------------------------------------------------------------------
-- Point-free first-order syntax
----------------------------------------------------------------------

--! CorePRFOSyntax {
data _→ᴾ_ : TY FO → TY FO → Set where
  -- category
  id        : T →ᴾ T
  C         : U →ᴾ V → T →ᴾ U → T →ᴾ V

  -- initial and terminal objects
  `⊤        : T →ᴾ `𝟙
  `⊥        : `𝟘 →ᴾ T

  -- products
  `#        : T →ᴾ U → T →ᴾ V → T →ᴾ U `× V
  π₁        : U `× V →ᴾ U
  π₂        : U `× V →ᴾ V

  -- sums
  ι₁        : U →ᴾ U `+ V
  ι₂        : V →ᴾ U `+ V
  `case    : U →ᴾ T → V →ᴾ T → U `+ V →ᴾ T

  -- distributivity
  dist-+-× : (U `+ V) `× T →ᴾ (U `× T) `+ (V `× T)

  -- functorial action and its right strength
  fmap      : (G : Ty FO 1) → (T →ᴾ U) → (G [ T ] →ᴾ G [ U ])
  strength  : (G : Ty FO 1) → (G [ T ]) `× U →ᴾ G [ T `× U ]

  -- inductive types and primitive recursion
  con      : G [ ind G ] →ᴾ ind G
  P         : (G [ T `× ind G ]) `× U →ᴾ T → ind G `× U →ᴾ T
--! }

--! CorePRFODerivedOperations {
map-× : U →ᴾ T → V →ᴾ W → U `× V →ᴾ T `× W
map-× f g = `# (C f π₁) (C g π₂)

pmap : (G : Ty FO 1) → (T `× U →ᴾ V)
  → ((G [ T ]) `× U →ᴾ G [ V ])
pmap G f = C (fmap G f) (strength G)

paraArgs : (G : Ty FO 1) → (ind G `× U →ᴾ T)
  → ((G [ ind G ]) `× U →ᴾ (G [ T `× ind G ]) `× U)
paraArgs G p = `# (pmap G (`# p π₁)) π₂
--! }

undist-+-× : (U `× T) `+ (V `× T) →ᴾ (U `+ V) `× T
undist-+-× = `case (`# (C ι₁ π₁) π₂) (`# (C ι₂ π₁) π₂)
