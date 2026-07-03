{-# OPTIONS --safe #-}

module Core.Equations.PRFOFold where

open import Core.PRFOFold public hiding (T; U; V; W; G)

infix 4 _≈_

----------------------------------------------------------------------
-- Equational theory for first-order PR with primitive catamorphism
----------------------------------------------------------------------

private
  variable
    A B D E S T U V : TY FO
    G H : Ty FO 1

data _≈_ : T →ᶠ U → T →ᶠ U → Set where
  ≈-refl  : {f : A →ᶠ B} → f ≈ f
  ≈-sym   : {f g : A →ᶠ B} → f ≈ g → g ≈ f
  ≈-trans : {f g h : A →ᶠ B}
    → f ≈ g → g ≈ h → f ≈ h

  C-cong :
    {f f′ : B →ᶠ D} {g g′ : A →ᶠ B}
    → f ≈ f′ → g ≈ g′ → C f g ≈ C f′ g′
  `#-cong :
    {f f′ : A →ᶠ B} {g g′ : A →ᶠ D}
    → f ≈ f′ → g ≈ g′ → `# f g ≈ `# f′ g′
  `case-cong :
    {f f′ : A →ᶠ D} {g g′ : B →ᶠ D}
    → f ≈ f′ → g ≈ g′ → `case f g ≈ `case f′ g′
  fmap-cong : ∀ {A B : TY FO} (H : Ty FO 1)
    {f f′ : A →ᶠ B} → f ≈ f′ → fmap H f ≈ fmap H f′
  F-cong : ∀ {A B : TY FO} {H : Ty FO 1}
    {h h′ : (H [ A ]) `× B →ᶠ A}
    → h ≈ h′
    → F {G = H} {T = A} {U = B} h ≈ F {G = H} {T = A} {U = B} h′

  C-idˡ : {f : A →ᶠ B}
    → C id f ≈ f
  C-idʳ : {f : A →ᶠ B}
    → C f id ≈ f
  C-assoc :
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

  𝟙-unique : {f : A →ᶠ `𝟙}
    → f ≈ `⊤
  𝟘-unique : {f : `𝟘 →ᶠ A}
    → f ≈ `⊥

  ×-β₁ : {f : A →ᶠ B} {g : A →ᶠ D}
    → C π₁ (`# f g) ≈ f
  ×-β₂ : {f : A →ᶠ B} {g : A →ᶠ D}
    → C π₂ (`# f g) ≈ g
  ×-η : {f : A →ᶠ B `× D}
    → `# (C π₁ f) (C π₂ f) ≈ f

  +-β₁ : {f : A →ᶠ D} {g : B →ᶠ D}
    → C (`case f g) ι₁ ≈ f
  +-β₂ : {f : A →ᶠ D} {g : B →ᶠ D}
    → C (`case f g) ι₂ ≈ g
  +-η : {f : A `+ B →ᶠ D}
    → `case (C f ι₁) (C f ι₂) ≈ f

  dist-undist :
    C (dist-+-× {U = A} {V = B} {T = D}) undist-+-× ≈ id
  undist-dist :
    C undist-+-× (dist-+-× {U = A} {V = B} {T = D}) ≈ id

  F-β : ∀ {A B : TY FO} {H : Ty FO 1}
    {h : (H [ A ]) `× B →ᶠ A}
    → C (F {G = H} {T = A} {U = B} h)
          (map-× (con {G = H}) (id {T = B}))
      ≈ C h (foldArgs H (F {G = H} {T = A} {U = B} h))

  F-unique : ∀ {A B : TY FO} {H : Ty FO 1}
    {h : (H [ A ]) `× B →ᶠ A}
    {p : ind H `× B →ᶠ A}
    → C p (map-× (con {G = H}) (id {T = B})) ≈ C h (foldArgs H p)
    → p ≈ F {G = H} {T = A} {U = B} h
