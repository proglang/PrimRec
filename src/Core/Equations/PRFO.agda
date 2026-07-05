{-# OPTIONS --safe #-}

module Core.Equations.PRFO where

open import Core.PRFO public

infix 4 _≈_

----------------------------------------------------------------------
-- Equational theory for PR-FO
--
-- Equality is generated inductively rather than by quotienting arrows.
-- The recursion laws use the parameterized functorial action defined by
-- pmap and paraArgs in Core.PRFO.
----------------------------------------------------------------------

--! CorePRFOEquivalence {
data _≈_ : T →ᴾ U → T →ᴾ U → Set where
  ≈-refl  : {f : A →ᴾ B} → f ≈ f
  ≈-sym   : {f g : A →ᴾ B} → f ≈ g → g ≈ f
  ≈-trans : {f g h : A →ᴾ B} → f ≈ g → g ≈ h → f ≈ h

  C-cong : {f f′ : B →ᴾ D} {g g′ : A →ᴾ B}
    → f ≈ f′ → g ≈ g′ → C f g ≈ C f′ g′
  `#-cong : {f f′ : A →ᴾ B} {g g′ : A →ᴾ D}
    → f ≈ f′ → g ≈ g′ → `# f g ≈ `# f′ g′
  `case-cong : {f f′ : A →ᴾ D} {g g′ : B →ᴾ D}
    → f ≈ f′ → g ≈ g′ → `case f g ≈ `case f′ g′
  fmap-cong : (H : Ty FO 1) {f f′ : A →ᴾ B}
    → f ≈ f′ → fmap H f ≈ fmap H f′
  P-cong : ∀ {A B : TY FO} {G : Ty FO 1}
    {h h′ : (G [ A `× ind G ]) `× B →ᴾ A}
    → h ≈ h′
    → P h ≈ P {G = G} h′
--! }

  C-idˡ : {f : A →ᴾ B}
    → C id f ≈ f
  C-idʳ : {f : A →ᴾ B}
    → C f id ≈ f
  C-assoc :
    {f : D →ᴾ E} {g : B →ᴾ D} {h : A →ᴾ B}
    → C f (C g h) ≈ C (C f g) h

  fmap-id : ∀ {A : TY FO} (H : Ty FO 1)
    → fmap H (id {T = A}) ≈ id
  fmap-C : ∀ {A B D : TY FO} (H : Ty FO 1)
    {f : B →ᴾ D} {g : A →ᴾ B}
    → fmap H (C f g) ≈ C (fmap H f) (fmap H g)

  strength-naturalˡ : ∀ {A B D : TY FO} (H : Ty FO 1)
    {f : A →ᴾ B}
    → C (fmap H (map-× f (id {T = D}))) (strength {T = A} {U = D} H)
      ≈ C (strength {T = B} {U = D} H) (map-× (fmap H f) id)
  strength-naturalʳ : ∀ {A B D : TY FO} (H : Ty FO 1)
    {g : B →ᴾ D}
    → C (fmap H (map-× (id {T = A}) g)) (strength {T = A} {U = B} H)
      ≈ C (strength {T = A} {U = D} H) (map-× id g)
  strength-π₁ : ∀ {A B : TY FO} (H : Ty FO 1)
    → C (fmap H (π₁ {U = A} {V = B})) (strength {T = A} {U = B} H)
      ≈ π₁

  𝟙-unique : {f : A →ᴾ `𝟙}
    → f ≈ `⊤
  𝟘-unique : {f : `𝟘 →ᴾ A}
    → f ≈ `⊥

  ×-β₁ : {f : A →ᴾ B} {g : A →ᴾ D}
    → C π₁ (`# f g) ≈ f
  ×-β₂ : {f : A →ᴾ B} {g : A →ᴾ D}
    → C π₂ (`# f g) ≈ g
  ×-η : {f : A →ᴾ B `× D}
    → `# (C π₁ f) (C π₂ f) ≈ f

  +-β₁ : {f : A →ᴾ D} {g : B →ᴾ D}
    → C (`case f g) ι₁ ≈ f
  +-β₂ : {f : A →ᴾ D} {g : B →ᴾ D}
    → C (`case f g) ι₂ ≈ g
  +-η : {f : A `+ B →ᴾ D}
    → `case (C f ι₁) (C f ι₂) ≈ f

  dist-undist :
    C (dist-+-× {U = A} {V = B} {T = D}) undist-+-× ≈ id
  undist-dist :
    C undist-+-× (dist-+-× {U = A} {V = B} {T = D}) ≈ id

  --! CorePRFOParaLaws {
  P-β : ∀ {A B : TY FO} {G : Ty FO 1}
    {h : (G [ A `× ind G ]) `× B →ᴾ A}
    → C (P h) (map-× (con {G = G}) id)
      ≈ C h (paraArgs G (P h))

  P-unique : ∀ {A B : TY FO} {G : Ty FO 1}
    {h : (G [ A `× ind G ]) `× B →ᴾ A} {p : ind G `× B →ᴾ A}
    → C p (map-× con id) ≈ C h (paraArgs G p)
    → p ≈ P h
  --! }
