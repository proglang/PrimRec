{-# OPTIONS --safe #-}

module Core.Equations.PRHO where

open import Core.PRHO public

infix 4 _≈_

----------------------------------------------------------------------
-- Equational theory for PR-HO
----------------------------------------------------------------------

private
  variable
    F I : TY HO

data _≈_ : T →ᴾ U → T →ᴾ U → Set where
  ≈-refl  : {f : A →ᴾ B} → f ≈ f
  ≈-sym   : {f g : A →ᴾ B} → f ≈ g → g ≈ f
  ≈-trans : {f g h : A →ᴾ B}
    → f ≈ g → g ≈ h → f ≈ h

  C-cong :
    {f f′ : B →ᴾ D} {g g′ : A →ᴾ B}
    → f ≈ f′ → g ≈ g′ → C f g ≈ C f′ g′
  `#-cong :
    {f f′ : A →ᴾ B} {g g′ : A →ᴾ D}
    → f ≈ f′ → g ≈ g′ → `# f g ≈ `# f′ g′
  `case-cong :
    {f f′ : A →ᴾ D} {g g′ : B →ᴾ D}
    → f ≈ f′ → g ≈ g′ → `case f g ≈ `case f′ g′
  lam-cong : {f f′ : A `× B →ᴾ D}
    → f ≈ f′ → lam f ≈ lam f′
  fmap-cong : ∀ {A B : TY HO} (H : Ty HO 1)
    {f f′ : A →ᴾ B} → f ≈ f′ → fmap H f ≈ fmap H f′
  P-cong : ∀ {A B : TY HO} {H : Ty HO 1}
    {h h′ : (H [ A `× ind H ]) `× B →ᴾ A}
    → h ≈ h′
    → P {G = H} {T = A} {U = B} h ≈ P {G = H} {T = A} {U = B} h′

  C-idˡ : {f : A →ᴾ B}
    → C id f ≈ f
  C-idʳ : {f : A →ᴾ B}
    → C f id ≈ f
  C-assoc :
    {f : D →ᴾ E} {g : B →ᴾ D} {h : A →ᴾ B}
    → C f (C g h) ≈ C (C f g) h

  fmap-id : ∀ {A : TY HO} (H : Ty HO 1)
    → fmap H (id {T = A}) ≈ id
  fmap-C : ∀ {A B D : TY HO} (H : Ty HO 1)
    {f : B →ᴾ D} {g : A →ᴾ B}
    → fmap H (C f g) ≈ C (fmap H f) (fmap H g)
  fmap-βᶜ : ∀ {A B : TY HO} {H : Ty HO 1}
    (S : StructuralFunctor H) {f : A →ᴾ B}
    → fmap H f ≈ fmapᶜ S f

  strength-naturalˡ : ∀ {A B D : TY HO} (H : Ty HO 1)
    {f : A →ᴾ B}
    → C (fmap H (map-× f (id {T = D}))) (strength {T = A} {U = D} H)
      ≈ C (strength {T = B} {U = D} H) (map-× (fmap H f) id)
  strength-naturalʳ : ∀ {A B D : TY HO} (H : Ty HO 1)
    {g : B →ᴾ D}
    → C (fmap H (map-× (id {T = A}) g)) (strength {T = A} {U = B} H)
      ≈ C (strength {T = A} {U = D} H) (map-× id g)
  strength-π₁ : ∀ {A B : TY HO} (H : Ty HO 1)
    → C (fmap H (π₁ {U = A} {V = B})) (strength {T = A} {U = B} H)
      ≈ π₁
  strength-βᶜ : ∀ {A B : TY HO} {H : Ty HO 1}
    (S : StructuralFunctor H)
    → strength {T = A} {U = B} H ≈ strengthᶜ S

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

  ⇒-β : {f : A `× B →ᴾ D}
    → theta (lam f) ≈ f
  ⇒-η : {f : A →ᴾ B `⇒ D}
    → lam (theta f) ≈ f

  P-β : ∀ {A B : TY HO} {H : Ty HO 1}
    {h : (H [ A `× ind H ]) `× B →ᴾ A}
    → C (P {G = H} {T = A} {U = B} h)
          (map-× (con {G = H}) (id {T = B}))
      ≈ C h (paraArgs H (P {G = H} {T = A} {U = B} h))

  P-unique : ∀ {A B : TY HO} {H : Ty HO 1}
    {h : (H [ A `× ind H ]) `× B →ᴾ A}
    {p : ind H `× B →ᴾ A}
    → C p (map-× (con {G = H}) (id {T = B})) ≈ C h (paraArgs H p)
    → p ≈ P {G = H} {T = A} {U = B} h

----------------------------------------------------------------------
-- Derived categorical infrastructure
----------------------------------------------------------------------

C-# :
  {f : B →ᴾ D} {g : B →ᴾ E} {h : A →ᴾ B} →
  C (`# f g) h ≈ `# (C f h) (C g h)
C-# =
  ≈-trans (≈-sym ×-η)
    (`#-cong
      (≈-trans C-assoc (C-cong ×-β₁ ≈-refl))
      (≈-trans C-assoc (C-cong ×-β₂ ≈-refl)))

C-case :
  {f : A →ᴾ D} {g : B →ᴾ D} {h : D →ᴾ E} →
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
  {f : B →ᴾ E} {g : D →ᴾ F}
  {h : A →ᴾ B} {k : A →ᴾ D} →
  C (map-× f g) (`# h k) ≈ `# (C f h) (C g k)
map-×-# =
  ≈-trans C-#
    (`#-cong
      (≈-trans (≈-sym C-assoc) (C-cong ≈-refl ×-β₁))
      (≈-trans (≈-sym C-assoc) (C-cong ≈-refl ×-β₂)))

map-×-cong :
  {f f′ : B →ᴾ E} {g g′ : D →ᴾ F} →
  f ≈ f′ → g ≈ g′ → map-× f g ≈ map-× f′ g′
map-×-cong f≈ g≈ =
  `#-cong (C-cong f≈ ≈-refl) (C-cong g≈ ≈-refl)

map-×-C :
  {f : B →ᴾ E} {g : D →ᴾ F}
  {h : A →ᴾ B} {k : I →ᴾ D} →
  C (map-× f g) (map-× h k) ≈ map-× (C f h) (C g k)
map-×-C =
  ≈-trans map-×-#
    (`#-cong C-assoc C-assoc)

theta-cong : {f g : A →ᴾ B `⇒ D} →
  f ≈ g → theta f ≈ theta g
theta-cong f≈ =
  C-cong ≈-refl (`#-cong (C-cong f≈ ≈-refl) ≈-refl)

theta-lam-ext : {f g : A `× B →ᴾ D} →
  lam f ≈ lam g → f ≈ g
theta-lam-ext f≈ =
  ≈-trans (≈-sym ⇒-β)
    (≈-trans (theta-cong f≈) ⇒-β)

map-×-precomp-left :
  {f : B →ᴾ D} {h : A →ᴾ B} →
  map-× (C f h) (id {T = E}) ≈
  C (map-× f id) (map-× h (id {T = E}))
map-×-precomp-left {E = E} =
  ≈-sym
    (≈-trans map-×-C
      (`#-cong ≈-refl
        (C-cong (C-idˡ {f = id {T = E}}) ≈-refl)))

theta-precomp :
  {f : B `× D →ᴾ E} {h : A →ᴾ B} →
  theta (C (lam f) h) ≈ C f (map-× h (id {T = D}))
theta-precomp =
  ≈-trans (C-cong ≈-refl map-×-precomp-left)
    (≈-trans C-assoc (C-cong ⇒-β ≈-refl))

lam-precomp :
  {f : B `× D →ᴾ E} {h : A →ᴾ B} →
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

P-βᶜ :
  ∀ {A B X : TY HO} {H : Ty HO 1}
  (S : StructuralFunctor H)
  {h : (H [ A `× ind H ]) `× B →ᴾ A}
  {x : X →ᴾ H [ ind H ]}
  {u : X →ᴾ B} →
  C (P {G = H} {T = A} {U = B} h) (`# (C con x) u)
    ≈
  C h
    (`#
      (C (fmapᶜ S (`# (P {G = H} {T = A} {U = B} h) π₁))
        (C (strengthᶜ S) (`# x u)))
      u)
P-βᶜ {A = A} {B = B} {H = H} S {h = h} {x = x} {u = u} =
  ≈-trans
    (C-cong ≈-refl constructor-input)
    (≈-trans C-assoc
      (≈-trans (C-cong P-β ≈-refl)
        (≈-trans (≈-sym C-assoc)
          (C-cong ≈-refl para-input))))
  where
  p : ind H `× B →ᴾ A
  p = P {G = H} {T = A} {U = B} h

  layer : _ →ᴾ H [ ind H ]
  layer = x

  parameter : _ →ᴾ B
  parameter = u

  constructor-input :
    `# (C con layer) parameter
      ≈ C (map-× con (id {T = B})) (`# layer parameter)
  constructor-input =
    ≈-sym
      (≈-trans map-×-#
        (`#-cong ≈-refl C-idˡ))

  para-layer :
    C (C (fmap H (`# p π₁)) (strength H)) (`# layer parameter)
      ≈
    C (fmapᶜ S (`# p π₁))
      (C (strengthᶜ S) (`# layer parameter))
  para-layer =
    ≈-trans (≈-sym C-assoc)
      (C-cong (fmap-βᶜ S)
        (C-cong (strength-βᶜ S) ≈-refl))

  para-input :
    C (paraArgs H p) (`# layer parameter)
      ≈
    `#
      (C (fmapᶜ S (`# p π₁))
        (C (strengthᶜ S) (`# layer parameter)))
      parameter
  para-input =
    ≈-trans C-#
      (`#-cong para-layer ×-β₂)

pmap-naturalʳ :
  ∀ {A B D E : TY HO} (G : Ty HO 1)
  {f : A `× B →ᴾ E} {k : D →ᴾ B} →
  C (pmap G f) (map-× (id {T = G [ A ]}) k)
    ≈ pmap G (C f (map-× (id {T = A}) k))
pmap-naturalʳ G {f = f} {k = k} =
  ≈-trans (≈-sym C-assoc)
    (≈-trans
      (C-cong ≈-refl (≈-sym (strength-naturalʳ G)))
      (≈-trans C-assoc
        (C-cong (≈-sym (fmap-C G)) ≈-refl)))

map-×-π₁ :
  ∀ {A B D E : TY HO} {f : A →ᴾ B} {g : D →ᴾ E} →
  C π₁ (map-× f g) ≈ C f π₁
map-×-π₁ = ×-β₁

map-×-π₂ :
  ∀ {A B D E : TY HO} {f : A →ᴾ B} {g : D →ᴾ E} →
  C π₂ (map-× f g) ≈ C g π₂
map-×-π₂ = ×-β₂

paraArgs-naturalʳ :
  ∀ {A B D : TY HO} (G : Ty HO 1)
  {p : ind G `× B →ᴾ A} {k : D →ᴾ B} →
  C (paraArgs G p) (map-× (id {T = G [ ind G ]}) k)
    ≈
  C (map-× (id {T = G [ A `× ind G ]}) k)
    (paraArgs G (C p (map-× (id {T = ind G}) k)))
paraArgs-naturalʳ G {p = p} {k = k} =
  ≈-trans C-#
    (≈-trans
      (`#-cong
        (≈-trans (pmap-naturalʳ G)
          (C-cong
            (fmap-cong G
              (≈-trans C-#
                (`#-cong ≈-refl
                  (≈-trans map-×-π₁ C-idˡ))))
            ≈-refl))
        map-×-π₂)
      (≈-sym
        (≈-trans map-×-#
          (`#-cong C-idˡ ≈-refl))))

map-×-parameter-square :
  ∀ {B D : TY HO} {G : Ty HO 1} {k : D →ᴾ B} →
  C (map-× (id {T = ind G}) k)
    (map-× (con {G = G}) (id {T = D}))
    ≈
  C (map-× (con {G = G}) (id {T = B}))
    (map-× (id {T = G [ ind G ]}) k)
map-×-parameter-square {k = k} =
  ≈-trans
    (≈-trans map-×-C (map-×-cong C-idˡ C-idʳ))
    (≈-sym
      (≈-trans map-×-C (map-×-cong C-idʳ C-idˡ)))

P-parameterʳ :
  ∀ {A B D : TY HO} {G : Ty HO 1}
  {h : (G [ A `× ind G ]) `× B →ᴾ A}
  {k : D →ᴾ B} →
  P {G = G} {T = A} {U = D}
    (C h (map-× (id {T = G [ A `× ind G ]}) k))
    ≈
  C (P {G = G} {T = A} {U = B} h)
    (map-× (id {T = ind G}) k)
P-parameterʳ {A = A} {B = B} {D = D} {G = G} {h = h} {k = k} =
  ≈-sym (P-unique premise)
  where
  p : ind G `× D →ᴾ A
  p = C (P {G = G} {T = A} {U = B} h)
        (map-× (id {T = ind G}) k)

  h′ : (G [ A `× ind G ]) `× D →ᴾ A
  h′ = C h (map-× (id {T = G [ A `× ind G ]}) k)

  premise :
    C p (map-× (con {G = G}) (id {T = D}))
      ≈ C h′ (paraArgs G p)
  premise =
    ≈-trans (≈-sym C-assoc)
      (≈-trans
        (C-cong ≈-refl map-×-parameter-square)
        (≈-trans C-assoc
          (≈-trans
            (C-cong P-β ≈-refl)
            (≈-trans (≈-sym C-assoc)
              (≈-trans
                (C-cong ≈-refl (paraArgs-naturalʳ G))
                C-assoc)))))
