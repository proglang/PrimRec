{-# OPTIONS --safe #-}

module Core.PRHO where

open import Core.Types public

infix 6 _→ᴾ_

variable
  T U V W : TY HO
  G : Ty HO 1

----------------------------------------------------------------------
-- Point-free higher-order syntax
----------------------------------------------------------------------

data _→ᴾ_ : TY HO → TY HO → Set where
  -- category
  id : T →ᴾ T
  C  : (U →ᴾ V) → (T →ᴾ U) → (T →ᴾ V)

  -- initial and terminal objects
  `⊤ : T →ᴾ `𝟙
  `⊥ : `𝟘 →ᴾ T

  -- products
  `# : (T →ᴾ U) → (T →ᴾ V) → (T →ᴾ U `× V)
  π₁ : U `× V →ᴾ U
  π₂ : U `× V →ᴾ V

  -- sums
  ι₁ : U →ᴾ U `+ V
  ι₂ : V →ᴾ U `+ V
  `case : (U →ᴾ T) → (V →ᴾ T) → (U `+ V →ᴾ T)

  --! CorePRHOExponentials {
  -- exponentials
  lam    : (U `× V →ᴾ T) → (U →ᴾ V `⇒ T)
  apply  : (T `⇒ U) `× T →ᴾ U
  --! }

  -- functorial action and its right strength
  fmap : (G : Ty HO 1) → (T →ᴾ U) → (G [ T ] →ᴾ G [ U ])
  strength : (G : Ty HO 1) → (G [ T ]) `× U →ᴾ G [ T `× U ]

  -- inductive types and primitive recursion
  roll : G [ ind G ] →ᴾ ind G
  P : ((G [ T `× ind G ]) `× U →ᴾ T)
    → (ind G `× U →ᴾ T)

--! CorePRHODerivedOperations {
map-× : (U →ᴾ T) → (V →ᴾ W) → (U `× V →ᴾ T `× W)
map-× f g = `# (C f π₁) (C g π₂)

pmap : (G : Ty HO 1) → (T `× U →ᴾ V)
  → ((G [ T ]) `× U →ᴾ G [ V ])
pmap G f = C (fmap G f) (strength G)

paraArgs : (G : Ty HO 1) → (ind G `× U →ᴾ T)
  → ((G [ ind G ]) `× U →ᴾ (G [ T `× ind G ]) `× U)
paraArgs G p = `# (pmap G (`# p π₁)) π₂
--! }

theta : (U →ᴾ V `⇒ T) → (U `× V →ᴾ T)
theta f = C apply (map-× f id)

--! CorePRHODerivedDist {
dist-+-× : (U `+ V) `× T →ᴾ (U `× T) `+ (V `× T)
dist-+-× = theta (`case (lam ι₁) (lam ι₂))
--! }

undist-+-× : (U `× T) `+ (V `× T) →ᴾ (U `+ V) `× T
undist-+-× = `case (`# (C ι₁ π₁) π₂) (`# (C ι₂ π₁) π₂)
