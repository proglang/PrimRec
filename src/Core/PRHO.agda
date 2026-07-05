{-# OPTIONS --safe #-}

module Core.PRHO where

open import Core.Types public

infix 6 _→ᴾ_

variable
  W : TY HO

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
  con : G [ ind G ] →ᴾ ind G
  P : ((G [ T `× ind G ]) `× U →ᴾ T)
    → (ind G `× U →ᴾ T)

--! CorePRHODerivedOperations {
map-× : (U →ᴾ T) → (V →ᴾ W) → (U `× V →ᴾ T `× W)
map-× f g = `# (C f π₁) (C g π₂)

fmapᶜ : ∀ {T U G} → StructuralFunctor G → (T →ᴾ U) → (G [ T ] →ᴾ G [ U ])
fmapᶜ sf-𝟘 f = id
fmapᶜ sf-𝟙 f = id
fmapᶜ sf-var f = f
fmapᶜ (sf-× p q) f = map-× (fmapᶜ p f) (fmapᶜ q f)
fmapᶜ (sf-+ p q) f =
  `case (C ι₁ (fmapᶜ p f)) (C ι₂ (fmapᶜ q f))
fmapᶜ (sf-⇒ A p) f = lam (C (fmapᶜ p f) apply)

pmap : (G : Ty HO 1) → (T `× U →ᴾ V)
  → ((G [ T ]) `× U →ᴾ G [ V ])
pmap G f = C (fmap G f) (strength G)

paraArgs : (G : Ty HO 1) → (ind G `× U →ᴾ T)
  → ((G [ ind G ]) `× U →ᴾ (G [ T `× ind G ]) `× U)
paraArgs G p = `# (pmap G (`# p π₁)) π₂
--! }

--! CorePRHODerivedDist {
theta : (U →ᴾ V `⇒ T) → (U `× V →ᴾ T)
theta f = C apply (map-× f id)

dist-+-× : (U `+ V) `× T →ᴾ (U `× T) `+ (V `× T)
dist-+-× = theta (`case (lam ι₁) (lam ι₂))
--! }

undist-+-× : (U `× T) `+ (V `× T) →ᴾ (U `+ V) `× T
undist-+-× = `case (`# (C ι₁ π₁) π₂) (`# (C ι₂ π₁) π₂)

strengthᶜ : ∀ {T U G} → StructuralFunctor G →
  (G [ T ]) `× U →ᴾ G [ T `× U ]
strengthᶜ sf-𝟘 = π₁
strengthᶜ sf-𝟙 = π₁
strengthᶜ sf-var = id
strengthᶜ (sf-× p q) =
  `#
    (C (strengthᶜ p) (`# (C π₁ π₁) π₂))
    (C (strengthᶜ q) (`# (C π₂ π₁) π₂))
strengthᶜ (sf-+ p q) =
  C (`case (C ι₁ (strengthᶜ p)) (C ι₂ (strengthᶜ q))) dist-+-×
strengthᶜ (sf-⇒ A p) =
  lam
    (C (strengthᶜ p)
      (`# (C apply (`# (C π₁ π₁) π₂))
          (C π₂ π₁)))
