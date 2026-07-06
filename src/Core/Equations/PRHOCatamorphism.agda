{-# OPTIONS --safe #-}

module Core.Equations.PRHOCatamorphism where

open import Core.PRHOCatamorphism public

infix 4 _≈_

----------------------------------------------------------------------
-- Equational theory for higher-order PR with primitive catamorphism
----------------------------------------------------------------------

private
  variable
    I R : TY HO

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
  lam-cong : {f f′ : A `× B →ᶜ D}
    → f ≈ f′ → lam f ≈ lam f′
  fmap-cong : ∀ {A B : TY HO} (H : Ty HO 1)
    {f f′ : A →ᶜ B} → f ≈ f′ → fmap H f ≈ fmap H f′
  Ct-cong : ∀ {A B : TY HO} {H : Ty HO 1}
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

  fmap-id : ∀ {A : TY HO} (H : Ty HO 1)
    → fmap H (id {T = A}) ≈ id
  fmap-C : ∀ {A B D : TY HO} (H : Ty HO 1)
    {f : B →ᶜ D} {g : A →ᶜ B}
    → fmap H (C f g) ≈ C (fmap H f) (fmap H g)
  fmap-βᶜ : ∀ {A B : TY HO} {H : Ty HO 1}
    (S : StructuralFunctor H) {f : A →ᶜ B}
    → fmap H f ≈ fmapᶜ S f

  strength-naturalˡ : ∀ {A B D : TY HO} (H : Ty HO 1)
    {f : A →ᶜ B}
    → C (fmap H (map-× f (id {T = D}))) (strength {T = A} {U = D} H)
      ≈ C (strength {T = B} {U = D} H) (map-× (fmap H f) id)
  strength-naturalʳ : ∀ {A B D : TY HO} (H : Ty HO 1)
    {g : B →ᶜ D}
    → C (fmap H (map-× (id {T = A}) g)) (strength {T = A} {U = B} H)
      ≈ C (strength {T = A} {U = D} H) (map-× id g)
  strength-π₁ : ∀ {A B : TY HO} (H : Ty HO 1)
    → C (fmap H (π₁ {U = A} {V = B})) (strength {T = A} {U = B} H)
      ≈ π₁
  strength-βᶜ : ∀ {A B : TY HO} {H : Ty HO 1}
    (S : StructuralFunctor H)
    → strength {T = A} {U = B} H ≈ strengthᶜ S

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

  ⇒-β : {f : A `× B →ᶜ D}
    → theta (lam f) ≈ f
  ⇒-η : {f : A →ᶜ B `⇒ D}
    → lam (theta f) ≈ f

  Ct-β : ∀ {A B : TY HO} {H : Ty HO 1}
    {h : (H [ A ]) `× B →ᶜ A}
    → C (Ct {G = H} {T = A} {U = B} h)
          (map-× (con {G = H}) (id {T = B}))
      ≈ C h (catamorphismArgs H (Ct {G = H} {T = A} {U = B} h))

  Ct-unique : ∀ {A B : TY HO} {H : Ty HO 1}
    {h : (H [ A ]) `× B →ᶜ A}
    {p : ind H `× B →ᶜ A}
    → C p (map-× (con {G = H}) (id {T = B})) ≈ C h (catamorphismArgs H p)
    → p ≈ Ct {G = H} {T = A} {U = B} h

----------------------------------------------------------------------
-- Small derived categorical infrastructure used by translations
----------------------------------------------------------------------

C-# :
  {f : B →ᶜ D} {g : B →ᶜ E} {h : A →ᶜ B} →
  C (`# f g) h ≈ `# (C f h) (C g h)
C-# =
  ≈-trans (≈-sym ×-η)
    (`#-cong
      (≈-trans C-assoc (C-cong ×-β₁ ≈-refl))
      (≈-trans C-assoc (C-cong ×-β₂ ≈-refl)))

map-×-cong :
  {f f′ : B →ᶜ E} {g g′ : D →ᶜ R} →
  f ≈ f′ → g ≈ g′ → map-× f g ≈ map-× f′ g′
map-×-cong f≈ g≈ =
  `#-cong (C-cong f≈ ≈-refl) (C-cong g≈ ≈-refl)

C-case :
  {f : A →ᶜ D} {g : B →ᶜ D} {h : D →ᶜ E} →
  C h (`case f g) ≈ `case (C h f) (C h g)
C-case =
  ≈-trans (≈-sym +-η)
    (`case-cong
      (≈-trans (≈-sym C-assoc) (C-cong ≈-refl +-β₁))
      (≈-trans (≈-sym C-assoc) (C-cong ≈-refl +-β₂)))

case-id : `case (ι₁ {U = A} {V = B}) ι₂ ≈ id
case-id =
  ≈-trans
    (`case-cong (≈-sym C-idˡ) (≈-sym C-idˡ))
    +-η

pair-id : `# (π₁ {U = A} {V = B}) π₂ ≈ id
pair-id =
  ≈-trans
    (`#-cong (≈-sym C-idʳ) (≈-sym C-idʳ))
    ×-η

map-×-# :
  {f : B →ᶜ E} {g : D →ᶜ R}
  {h : A →ᶜ B} {k : A →ᶜ D} →
  C (map-× f g) (`# h k) ≈ `# (C f h) (C g k)
map-×-# =
  ≈-trans C-#
    (`#-cong
      (≈-trans (≈-sym C-assoc) (C-cong ≈-refl ×-β₁))
      (≈-trans (≈-sym C-assoc) (C-cong ≈-refl ×-β₂)))

map-×-C :
  {f : B →ᶜ E} {g : D →ᶜ R}
  {h : A →ᶜ B} {k : I →ᶜ D} →
  C (map-× f g) (map-× h k) ≈ map-× (C f h) (C g k)
map-×-C =
  ≈-trans map-×-#
    (`#-cong C-assoc C-assoc)

theta-cong : {f g : A →ᶜ B `⇒ D} →
  f ≈ g → theta f ≈ theta g
theta-cong f≈ =
  C-cong ≈-refl (`#-cong (C-cong f≈ ≈-refl) ≈-refl)

theta-lam-ext : {f g : A `× B →ᶜ D} →
  lam f ≈ lam g → f ≈ g
theta-lam-ext f≈ =
  ≈-trans (≈-sym ⇒-β)
    (≈-trans (theta-cong f≈) ⇒-β)

map-×-precomp-left :
  {f : B →ᶜ D} {h : A →ᶜ B} →
  map-× (C f h) (id {T = E}) ≈
  C (map-× f id) (map-× h (id {T = E}))
map-×-precomp-left {E = E} =
  ≈-sym
    (≈-trans map-×-C
      (`#-cong ≈-refl
        (C-cong (C-idˡ {f = id {T = E}}) ≈-refl)))

theta-precomp :
  {f : B `× D →ᶜ E} {h : A →ᶜ B} →
  theta (C (lam f) h) ≈ C f (map-× h (id {T = D}))
theta-precomp =
  ≈-trans (C-cong ≈-refl map-×-precomp-left)
    (≈-trans C-assoc (C-cong ⇒-β ≈-refl))

lam-precomp :
  {f : B `× D →ᶜ E} {h : A →ᶜ B} →
  C (lam f) h ≈ lam (C f (map-× h (id {T = D})))
lam-precomp =
  ≈-trans (≈-sym ⇒-η) (lam-cong theta-precomp)

dist-ι₁ :
  C (dist-+-× {U = A} {V = B} {T = D})
    (`# (C ι₁ π₁) π₂) ≈ ι₁
dist-ι₁ =
  ≈-trans (≈-sym C-assoc)
    (≈-trans (C-cong ≈-refl map-×-#)
      (≈-trans
        (C-cong ≈-refl
          (`#-cong
            (≈-trans C-assoc (C-cong +-β₁ ≈-refl))
            ≈-refl))
        ⇒-β))

dist-ι₂ :
  C (dist-+-× {U = A} {V = B} {T = D})
    (`# (C ι₂ π₁) π₂) ≈ ι₂
dist-ι₂ =
  ≈-trans (≈-sym C-assoc)
    (≈-trans (C-cong ≈-refl map-×-#)
      (≈-trans
        (C-cong ≈-refl
          (`#-cong
            (≈-trans C-assoc (C-cong +-β₂ ≈-refl))
            ≈-refl))
        ⇒-β))

dist-undist :
  C (dist-+-× {U = A} {V = B} {T = D}) undist-+-× ≈ id
dist-undist =
  ≈-trans (≈-sym +-η)
    (≈-trans
      (`case-cong
        (≈-trans (≈-sym C-assoc)
          (≈-trans (C-cong ≈-refl +-β₁) dist-ι₁))
        (≈-trans (≈-sym C-assoc)
          (≈-trans (C-cong ≈-refl +-β₂) dist-ι₂)))
      case-id)

dist-map-ι₁ :
  C (dist-+-× {U = A} {V = B} {T = D})
    (map-× ι₁ (id {T = D})) ≈ ι₁
dist-map-ι₁ =
  ≈-trans
    (C-cong ≈-refl
      (`#-cong ≈-refl (C-idˡ {f = π₂})))
    dist-ι₁

dist-map-ι₂ :
  C (dist-+-× {U = A} {V = B} {T = D})
    (map-× ι₂ (id {T = D})) ≈ ι₂
dist-map-ι₂ =
  ≈-trans
    (C-cong ≈-refl
      (`#-cong ≈-refl (C-idˡ {f = π₂})))
    dist-ι₂

project₁-after-dist :
  C (`case (C ι₁ π₁) (C ι₂ π₁))
    (dist-+-× {U = A} {V = B} {T = D})
  ≈ π₁
project₁-after-dist =
  theta-lam-ext
    (≈-trans (≈-sym +-η)
      (≈-trans
        (`case-cong branch₁ branch₂)
        +-η))
  where
  q-ι₁ :
    C (C (`case (C ι₁ π₁) (C ι₂ π₁))
         (dist-+-× {U = A} {V = B} {T = D}))
      (map-× ι₁ id)
    ≈ C ι₁ π₁
  q-ι₁ =
    ≈-trans (≈-sym C-assoc)
      (≈-trans (C-cong ≈-refl dist-map-ι₁) +-β₁)

  q-ι₂ :
    C (C (`case (C ι₁ π₁) (C ι₂ π₁))
         (dist-+-× {U = A} {V = B} {T = D}))
      (map-× ι₂ id)
    ≈ C ι₂ π₁
  q-ι₂ =
    ≈-trans (≈-sym C-assoc)
      (≈-trans (C-cong ≈-refl dist-map-ι₂) +-β₂)

  π₁-ι₁ :
    C (π₁ {U = A `+ B} {V = D}) (map-× ι₁ id) ≈ C ι₁ π₁
  π₁-ι₁ = ×-β₁

  π₁-ι₂ :
    C (π₁ {U = A `+ B} {V = D}) (map-× ι₂ id) ≈ C ι₂ π₁
  π₁-ι₂ = ×-β₁

  branch₁ :
    C (lam
        (C (`case (C ι₁ π₁) (C ι₂ π₁))
          (dist-+-× {U = A} {V = B} {T = D})))
      ι₁
    ≈
    C (lam (π₁ {U = A `+ B} {V = D})) ι₁
  branch₁ =
    ≈-trans
      (≈-trans lam-precomp (lam-cong q-ι₁))
      (≈-sym (≈-trans lam-precomp (lam-cong π₁-ι₁)))

  branch₂ :
    C (lam
        (C (`case (C ι₁ π₁) (C ι₂ π₁))
          (dist-+-× {U = A} {V = B} {T = D})))
      ι₂
    ≈
    C (lam (π₁ {U = A `+ B} {V = D})) ι₂
  branch₂ =
    ≈-trans
      (≈-trans lam-precomp (lam-cong q-ι₂))
      (≈-sym (≈-trans lam-precomp (lam-cong π₁-ι₂)))

project₂-after-dist :
  C (`case (π₂ {U = A} {V = D}) (π₂ {U = B} {V = D}))
    (dist-+-× {U = A} {V = B} {T = D})
  ≈ π₂
project₂-after-dist =
  theta-lam-ext
    (≈-trans (≈-sym +-η)
      (≈-trans
        (`case-cong branch₁ branch₂)
        +-η))
  where
  q-ι₁ :
    C (C (`case (π₂ {U = A} {V = D}) (π₂ {U = B} {V = D}))
         (dist-+-× {U = A} {V = B} {T = D}))
      (map-× ι₁ id)
    ≈ π₂
  q-ι₁ =
    ≈-trans (≈-sym C-assoc)
      (≈-trans (C-cong ≈-refl dist-map-ι₁) +-β₁)

  q-ι₂ :
    C (C (`case (π₂ {U = A} {V = D}) (π₂ {U = B} {V = D}))
         (dist-+-× {U = A} {V = B} {T = D}))
      (map-× ι₂ id)
    ≈ π₂
  q-ι₂ =
    ≈-trans (≈-sym C-assoc)
      (≈-trans (C-cong ≈-refl dist-map-ι₂) +-β₂)

  π₂-ι₁ :
    C (π₂ {U = A `+ B} {V = D}) (map-× ι₁ id) ≈ π₂
  π₂-ι₁ =
    ≈-trans ×-β₂ C-idˡ

  π₂-ι₂ :
    C (π₂ {U = A `+ B} {V = D}) (map-× ι₂ id) ≈ π₂
  π₂-ι₂ =
    ≈-trans ×-β₂ C-idˡ

  branch₁ :
    C (lam
        (C (`case (π₂ {U = A} {V = D}) (π₂ {U = B} {V = D}))
          (dist-+-× {U = A} {V = B} {T = D})))
      ι₁
    ≈
    C (lam (π₂ {U = A `+ B} {V = D})) ι₁
  branch₁ =
    ≈-trans
      (≈-trans lam-precomp (lam-cong q-ι₁))
      (≈-sym (≈-trans lam-precomp (lam-cong π₂-ι₁)))

  branch₂ :
    C (lam
        (C (`case (π₂ {U = A} {V = D}) (π₂ {U = B} {V = D}))
          (dist-+-× {U = A} {V = B} {T = D})))
      ι₂
    ≈
    C (lam (π₂ {U = A `+ B} {V = D})) ι₂
  branch₂ =
    ≈-trans
      (≈-trans lam-precomp (lam-cong q-ι₂))
      (≈-sym (≈-trans lam-precomp (lam-cong π₂-ι₂)))

π₁-undist :
  C π₁ (undist-+-× {D} {A} {B})
  ≈ `case (C ι₁ π₁) (C ι₂ π₁)
π₁-undist =
  ≈-trans C-case
    (`case-cong ×-β₁ ×-β₁)

π₂-undist :
  C π₂ (undist-+-× {D} {A} {B})
  ≈ `case π₂ π₂
π₂-undist =
  ≈-trans C-case
    (`case-cong ×-β₂ ×-β₂)

undist-dist :
  C undist-+-× (dist-+-× {U = A} {V = B} {T = D}) ≈ id
undist-dist =
  ≈-trans (≈-sym ×-η)
    (≈-trans
      (`#-cong
        (≈-trans C-assoc
          (≈-trans (C-cong π₁-undist ≈-refl) project₁-after-dist))
        (≈-trans C-assoc
          (≈-trans (C-cong π₂-undist ≈-refl) project₂-after-dist)))
      pair-id)
