{-# OPTIONS --safe #-}

module Core.Equations.PRFOCatamorphism where

open import Core.PRFOCatamorphism public

infix 4 _≈_

----------------------------------------------------------------------
-- Equational theory for first-order PR with primitive catamorphism
----------------------------------------------------------------------

data _≈_ : T →ᶜ U → T →ᶜ U → Set where
  ≈-refl  : {f : A →ᶜ B} → f ≈ f
  ≈-sym   : {f g : A →ᶜ B} → f ≈ g → g ≈ f
  ≈-trans : {f g h : A →ᶜ B}
    → f ≈ g → g ≈ h → f ≈ h

  C-cong :
    {f f′ : B →ᶜ D} {g g′ : A →ᶜ B}
    → f ≈ f′ → g ≈ g′ → C f g ≈ C f′ g′
  `#-cong :
    {f f′ : A →ᶜ B} {g g′ : A →ᶜ D}
    → f ≈ f′ → g ≈ g′ → `# f g ≈ `# f′ g′
  `case-cong :
    {f f′ : A →ᶜ D} {g g′ : B →ᶜ D}
    → f ≈ f′ → g ≈ g′ → `case f g ≈ `case f′ g′
  fmap-cong : ∀ {A B : TY FO} (H : Ty FO 1)
    {f f′ : A →ᶜ B} → f ≈ f′ → fmap H f ≈ fmap H f′
  Ct-cong : ∀ {A B : TY FO} {H : Ty FO 1}
    {h h′ : (H [ A ]) `× B →ᶜ A}
    → h ≈ h′
    → Ct {G = H} {T = A} {U = B} h ≈ Ct {G = H} {T = A} {U = B} h′

  C-idˡ : {f : A →ᶜ B}
    → C id f ≈ f
  C-idʳ : {f : A →ᶜ B}
    → C f id ≈ f
  C-assoc :
    {f : D →ᶜ E} {g : B →ᶜ D} {h : A →ᶜ B}
    → C f (C g h) ≈ C (C f g) h

  fmap-id : ∀ {A : TY FO} (H : Ty FO 1)
    → fmap H (id {T = A}) ≈ id
  fmap-C : ∀ {A B D : TY FO} (H : Ty FO 1)
    {f : B →ᶜ D} {g : A →ᶜ B}
    → fmap H (C f g) ≈ C (fmap H f) (fmap H g)

  strength-naturalˡ : ∀ {A B D : TY FO} (H : Ty FO 1)
    {f : A →ᶜ B}
    → C (fmap H (map-× f (id {T = D}))) (strength {T = A} {U = D} H)
      ≈ C (strength {T = B} {U = D} H) (map-× (fmap H f) id)
  strength-naturalʳ : ∀ {A B D : TY FO} (H : Ty FO 1)
    {g : B →ᶜ D}
    → C (fmap H (map-× (id {T = A}) g)) (strength {T = A} {U = B} H)
      ≈ C (strength {T = A} {U = D} H) (map-× id g)
  strength-π₁ : ∀ {A B : TY FO} (H : Ty FO 1)
    → C (fmap H (π₁ {U = A} {V = B})) (strength {T = A} {U = B} H)
      ≈ π₁

  𝟙-unique : {f : A →ᶜ `𝟙}
    → f ≈ `⊤
  𝟘-unique : {f : `𝟘 →ᶜ A}
    → f ≈ `⊥

  ×-β₁ : {f : A →ᶜ B} {g : A →ᶜ D}
    → C π₁ (`# f g) ≈ f
  ×-β₂ : {f : A →ᶜ B} {g : A →ᶜ D}
    → C π₂ (`# f g) ≈ g
  ×-η : {f : A →ᶜ B `× D}
    → `# (C π₁ f) (C π₂ f) ≈ f

  +-β₁ : {f : A →ᶜ D} {g : B →ᶜ D}
    → C (`case f g) ι₁ ≈ f
  +-β₂ : {f : A →ᶜ D} {g : B →ᶜ D}
    → C (`case f g) ι₂ ≈ g
  +-η : {f : A `+ B →ᶜ D}
    → `case (C f ι₁) (C f ι₂) ≈ f

  dist-undist :
    C (dist-+-× {U = A} {V = B} {T = D}) undist-+-× ≈ id
  undist-dist :
    C undist-+-× (dist-+-× {U = A} {V = B} {T = D}) ≈ id

  Ct-β : ∀ {A B : TY FO} {H : Ty FO 1}
    {h : (H [ A ]) `× B →ᶜ A}
    → C (Ct {G = H} {T = A} {U = B} h)
          (map-× (con {G = H}) (id {T = B}))
      ≈ C h (catamorphismArgs H (Ct {G = H} {T = A} {U = B} h))

  Ct-unique : ∀ {A B : TY FO} {H : Ty FO 1}
    {h : (H [ A ]) `× B →ᶜ A}
    {p : ind H `× B →ᶜ A}
    → C p (map-× (con {G = H}) (id {T = B})) ≈ C h (catamorphismArgs H p)
    → p ≈ Ct {G = H} {T = A} {U = B} h
