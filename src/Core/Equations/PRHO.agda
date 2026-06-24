{-# OPTIONS --safe #-}

module Core.Equations.PRHO where

open import Core.PRHO public

infix 4 _≈_

----------------------------------------------------------------------
-- Equational theory for PR-HO
----------------------------------------------------------------------

data _≈_ : ∀ {T U : TY HO} → T →ᴾ U → T →ᴾ U → Set where
  ≈-refl  : ∀ {A B : TY HO} {f : A →ᴾ B} → f ≈ f
  ≈-sym   : ∀ {A B : TY HO} {f g : A →ᴾ B} → f ≈ g → g ≈ f
  ≈-trans : ∀ {A B : TY HO} {f g h : A →ᴾ B}
    → f ≈ g → g ≈ h → f ≈ h

  C-cong : ∀ {A B D : TY HO}
    {f f′ : B →ᴾ D} {g g′ : A →ᴾ B}
    → f ≈ f′ → g ≈ g′ → C f g ≈ C f′ g′
  `#-cong : ∀ {A B D : TY HO}
    {f f′ : A →ᴾ B} {g g′ : A →ᴾ D}
    → f ≈ f′ → g ≈ g′ → `# f g ≈ `# f′ g′
  `case-cong : ∀ {A B D : TY HO}
    {f f′ : A →ᴾ D} {g g′ : B →ᴾ D}
    → f ≈ f′ → g ≈ g′ → `case f g ≈ `case f′ g′
  lam-cong : ∀ {A B D : TY HO} {f f′ : A `× B →ᴾ D}
    → f ≈ f′ → lam f ≈ lam f′
  fmap-cong : ∀ {A B : TY HO} (H : Ty HO 1)
    {f f′ : A →ᴾ B} → f ≈ f′ → fmap H f ≈ fmap H f′
  P-cong : ∀ {A B : TY HO} {H : Ty HO 1}
    {h h′ : (H ⇐ (A `× ind H)) `× B →ᴾ A}
    → h ≈ h′
    → P {G = H} {T = A} {U = B} h ≈ P {G = H} {T = A} {U = B} h′

  C-idˡ : ∀ {A B : TY HO} {f : A →ᴾ B}
    → C id f ≈ f
  C-idʳ : ∀ {A B : TY HO} {f : A →ᴾ B}
    → C f id ≈ f
  C-assoc : ∀ {A B D E : TY HO}
    {f : D →ᴾ E} {g : B →ᴾ D} {h : A →ᴾ B}
    → C f (C g h) ≈ C (C f g) h

  fmap-id : ∀ {A : TY HO} (H : Ty HO 1)
    → fmap H (id {T = A}) ≈ id
  fmap-C : ∀ {A B D : TY HO} (H : Ty HO 1)
    {f : B →ᴾ D} {g : A →ᴾ B}
    → fmap H (C f g) ≈ C (fmap H f) (fmap H g)

  strength-naturalˡ : ∀ {A B D : TY HO} (H : Ty HO 1)
    {f : A →ᴾ B}
    → C (fmap H (map-× f (id {T = D}))) (strength {T = A} {U = D} H)
      ≈ C (strength {T = B} {U = D} H) (map-× (fmap H f) id)
  strength-naturalʳ : ∀ {A B D : TY HO} (H : Ty HO 1)
    {g : B →ᴾ D}
    → C (fmap H (map-× (id {T = A}) g)) (strength {T = A} {U = B} H)
      ≈ C (strength {T = A} {U = D} H) (map-× id g)

  𝟙-unique : ∀ {A : TY HO} {f : A →ᴾ `𝟙}
    → f ≈ `⊤
  𝟘-unique : ∀ {A : TY HO} {f : `𝟘 →ᴾ A}
    → f ≈ `⊥

  ×-β₁ : ∀ {A B D : TY HO} {f : A →ᴾ B} {g : A →ᴾ D}
    → C π₁ (`# f g) ≈ f
  ×-β₂ : ∀ {A B D : TY HO} {f : A →ᴾ B} {g : A →ᴾ D}
    → C π₂ (`# f g) ≈ g
  ×-η : ∀ {A B D : TY HO} {f : A →ᴾ B `× D}
    → `# (C π₁ f) (C π₂ f) ≈ f

  +-β₁ : ∀ {A B D : TY HO} {f : A →ᴾ D} {g : B →ᴾ D}
    → C (`case f g) ι₁ ≈ f
  +-β₂ : ∀ {A B D : TY HO} {f : A →ᴾ D} {g : B →ᴾ D}
    → C (`case f g) ι₂ ≈ g
  +-η : ∀ {A B D : TY HO} {f : A `+ B →ᴾ D}
    → `case (C f ι₁) (C f ι₂) ≈ f

  ⇒-β : ∀ {A B D : TY HO} {f : A `× B →ᴾ D}
    → theta (lam f) ≈ f
  ⇒-η : ∀ {A B D : TY HO} {f : A →ᴾ B `⇒ D}
    → lam (theta f) ≈ f

  P-β : ∀ {A B : TY HO} {H : Ty HO 1}
    {h : (H ⇐ (A `× ind H)) `× B →ᴾ A}
    → C (P {G = H} {T = A} {U = B} h)
          (map-× (fold {G = H}) (id {T = B}))
      ≈ C h (paraArgs H (P {G = H} {T = A} {U = B} h))

  P-unique : ∀ {A B : TY HO} {H : Ty HO 1}
    {h : (H ⇐ (A `× ind H)) `× B →ᴾ A}
    {p : ind H `× B →ᴾ A}
    → C p (map-× (fold {G = H}) (id {T = B})) ≈ C h (paraArgs H p)
    → p ≈ P {G = H} {T = A} {U = B} h

-- The two inverse laws for dist-+-× are intended to be derived from
-- the bicartesian closed laws above, rather than added as axioms.
