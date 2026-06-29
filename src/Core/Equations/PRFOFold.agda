{-# OPTIONS --safe #-}

module Core.Equations.PRFOFold where

open import Core.PRFOFold public

infix 4 _≈_

----------------------------------------------------------------------
-- Equational theory for first-order PR with primitive catamorphism
----------------------------------------------------------------------

data _≈_ : ∀ {T U : TY FO} → T →ᶠ U → T →ᶠ U → Set where
  ≈-refl  : ∀ {A B : TY FO} {f : A →ᶠ B} → f ≈ f
  ≈-sym   : ∀ {A B : TY FO} {f g : A →ᶠ B} → f ≈ g → g ≈ f
  ≈-trans : ∀ {A B : TY FO} {f g h : A →ᶠ B}
    → f ≈ g → g ≈ h → f ≈ h

  C-cong : ∀ {A B D : TY FO}
    {f f′ : B →ᶠ D} {g g′ : A →ᶠ B}
    → f ≈ f′ → g ≈ g′ → C f g ≈ C f′ g′
  `#-cong : ∀ {A B D : TY FO}
    {f f′ : A →ᶠ B} {g g′ : A →ᶠ D}
    → f ≈ f′ → g ≈ g′ → `# f g ≈ `# f′ g′
  `case-cong : ∀ {A B D : TY FO}
    {f f′ : A →ᶠ D} {g g′ : B →ᶠ D}
    → f ≈ f′ → g ≈ g′ → `case f g ≈ `case f′ g′
  fmap-cong : ∀ {A B : TY FO} (H : Ty FO 1)
    {f f′ : A →ᶠ B} → f ≈ f′ → fmap H f ≈ fmap H f′
  F-cong : ∀ {A B : TY FO} {H : Ty FO 1}
    {h h′ : (H ⇐ A) `× B →ᶠ A}
    → h ≈ h′
    → F {G = H} {T = A} {U = B} h ≈ F {G = H} {T = A} {U = B} h′

  C-idˡ : ∀ {A B : TY FO} {f : A →ᶠ B}
    → C id f ≈ f
  C-idʳ : ∀ {A B : TY FO} {f : A →ᶠ B}
    → C f id ≈ f
  C-assoc : ∀ {A B D E : TY FO}
    {f : D →ᶠ E} {g : B →ᶠ D} {h : A →ᶠ B}
    → C f (C g h) ≈ C (C f g) h

  fmap-id : ∀ {A : TY FO} (H : Ty FO 1)
    → fmap H (id {T = A}) ≈ id
  fmap-C : ∀ {A B D : TY FO} (H : Ty FO 1)
    {f : B →ᶠ D} {g : A →ᶠ B}
    → fmap H (C f g) ≈ C (fmap H f) (fmap H g)

  strength-naturalˡ : ∀ {A B D : TY FO} (H : Ty FO 1)
    {f : A →ᶠ B}
    → C (fmap H (map-× f (id {T = D}))) (strength {T = A} {U = D} H)
      ≈ C (strength {T = B} {U = D} H) (map-× (fmap H f) id)
  strength-naturalʳ : ∀ {A B D : TY FO} (H : Ty FO 1)
    {g : B →ᶠ D}
    → C (fmap H (map-× (id {T = A}) g)) (strength {T = A} {U = B} H)
      ≈ C (strength {T = A} {U = D} H) (map-× id g)
  strength-π₁ : ∀ {A B : TY FO} (H : Ty FO 1)
    → C (fmap H (π₁ {U = A} {V = B})) (strength {T = A} {U = B} H)
      ≈ π₁

  𝟙-unique : ∀ {A : TY FO} {f : A →ᶠ `𝟙}
    → f ≈ `⊤
  𝟘-unique : ∀ {A : TY FO} {f : `𝟘 →ᶠ A}
    → f ≈ `⊥

  ×-β₁ : ∀ {A B D : TY FO} {f : A →ᶠ B} {g : A →ᶠ D}
    → C π₁ (`# f g) ≈ f
  ×-β₂ : ∀ {A B D : TY FO} {f : A →ᶠ B} {g : A →ᶠ D}
    → C π₂ (`# f g) ≈ g
  ×-η : ∀ {A B D : TY FO} {f : A →ᶠ B `× D}
    → `# (C π₁ f) (C π₂ f) ≈ f

  +-β₁ : ∀ {A B D : TY FO} {f : A →ᶠ D} {g : B →ᶠ D}
    → C (`case f g) ι₁ ≈ f
  +-β₂ : ∀ {A B D : TY FO} {f : A →ᶠ D} {g : B →ᶠ D}
    → C (`case f g) ι₂ ≈ g
  +-η : ∀ {A B D : TY FO} {f : A `+ B →ᶠ D}
    → `case (C f ι₁) (C f ι₂) ≈ f

  dist-undist : ∀ {A B D : TY FO}
    → C (dist-+-× {U = A} {V = B} {T = D}) undist-+-× ≈ id
  undist-dist : ∀ {A B D : TY FO}
    → C undist-+-× (dist-+-× {U = A} {V = B} {T = D}) ≈ id

  F-β : ∀ {A B : TY FO} {H : Ty FO 1}
    {h : (H ⇐ A) `× B →ᶠ A}
    → C (F {G = H} {T = A} {U = B} h)
          (map-× (fold {G = H}) (id {T = B}))
      ≈ C h (foldArgs H (F {G = H} {T = A} {U = B} h))

  F-unique : ∀ {A B : TY FO} {H : Ty FO 1}
    {h : (H ⇐ A) `× B →ᶠ A}
    {p : ind H `× B →ᶠ A}
    → C p (map-× (fold {G = H}) (id {T = B})) ≈ C h (foldArgs H p)
    → p ≈ F {G = H} {T = A} {U = B} h
