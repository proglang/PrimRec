{-# OPTIONS --safe #-}

module Core.Models.PRHOFold where

open import Level using (Level; suc)
open import Core.Types
import Core.PRHOFold as Syn
import Core.Equations.PRHOFold as Eq

----------------------------------------------------------------------
-- Raw PR-HO fold-primitive structures over the object-language types
----------------------------------------------------------------------

record Structure (ℓ : Level) : Set (suc ℓ) where
  infix 6 _⇒ᴹ_
  field
    _⇒ᴹ_ : TY HO → TY HO → Set ℓ

    idᴹ : ∀ {T} → T ⇒ᴹ T
    Cᴹ  : ∀ {T U V} → (U ⇒ᴹ V) → (T ⇒ᴹ U) → (T ⇒ᴹ V)

    ⊤ᴹ : ∀ {T} → T ⇒ᴹ `𝟙
    ⊥ᴹ : ∀ {T} → `𝟘 ⇒ᴹ T

    pairᴹ : ∀ {T U V} → (T ⇒ᴹ U) → (T ⇒ᴹ V) → (T ⇒ᴹ U `× V)
    π₁ᴹ : ∀ {T U} → T `× U ⇒ᴹ T
    π₂ᴹ : ∀ {T U} → T `× U ⇒ᴹ U

    ι₁ᴹ : ∀ {T U} → T ⇒ᴹ T `+ U
    ι₂ᴹ : ∀ {T U} → U ⇒ᴹ T `+ U
    caseᴹ : ∀ {T U V} → (T ⇒ᴹ V) → (U ⇒ᴹ V) → (T `+ U ⇒ᴹ V)

    lamᴹ : ∀ {T U V} → (T `× U ⇒ᴹ V) → (T ⇒ᴹ U `⇒ V)
    applyᴹ : ∀ {T U} → (T `⇒ U) `× T ⇒ᴹ U

    fmapᴹ : ∀ {T U} (G : Ty HO 1) → (T ⇒ᴹ U) → (G ⇐ T ⇒ᴹ G ⇐ U)
    strengthᴹ : ∀ {T U} (G : Ty HO 1) → (G ⇐ T) `× U ⇒ᴹ G ⇐ (T `× U)

    foldᴹ : ∀ {G : Ty HO 1} → G ⇐ ind G ⇒ᴹ ind G
    Fᴹ : ∀ {T U} {G : Ty HO 1}
      → ((G ⇐ T) `× U ⇒ᴹ T)
      → (ind G `× U ⇒ᴹ T)

module _ {ℓ} (S : Structure ℓ) where
  open Structure S

  map-×ᴹ : ∀ {T U V W}
    → (U ⇒ᴹ T) → (V ⇒ᴹ W) → (U `× V ⇒ᴹ T `× W)
  map-×ᴹ f g = pairᴹ (Cᴹ f π₁ᴹ) (Cᴹ g π₂ᴹ)

  pmapᴹ : ∀ {T U V} (G : Ty HO 1)
    → (T `× U ⇒ᴹ V) → ((G ⇐ T) `× U ⇒ᴹ G ⇐ V)
  pmapᴹ G f = Cᴹ (fmapᴹ G f) (strengthᴹ G)

  foldArgsᴹ : ∀ {T U} (G : Ty HO 1)
    → (ind G `× U ⇒ᴹ T)
    → ((G ⇐ ind G) `× U ⇒ᴹ (G ⇐ T) `× U)
  foldArgsᴹ G p = pairᴹ (pmapᴹ G p) π₂ᴹ

  thetaᴹ : ∀ {T U V} → (T ⇒ᴹ U `⇒ V) → (T `× U ⇒ᴹ V)
  thetaᴹ f = Cᴹ applyᴹ (map-×ᴹ f idᴹ)

  distᴹ : ∀ {T U V} → (T `+ U) `× V ⇒ᴹ (T `× V) `+ (U `× V)
  distᴹ = thetaᴹ (caseᴹ (lamᴹ ι₁ᴹ) (lamᴹ ι₂ᴹ))

  undistᴹ : ∀ {T U V} → (T `× V) `+ (U `× V) ⇒ᴹ (T `+ U) `× V
  undistᴹ = caseᴹ
    (pairᴹ (Cᴹ ι₁ᴹ π₁ᴹ) π₂ᴹ)
    (pairᴹ (Cᴹ ι₂ᴹ π₁ᴹ) π₂ᴹ)

----------------------------------------------------------------------
-- Law-bearing PR-HO fold-primitive models
----------------------------------------------------------------------

record Model (ℓ : Level) : Set (suc ℓ) where
  infix 4 _≈ᴹ_
  field
    structure : Structure ℓ

  open Structure structure public

  field
    _≈ᴹ_ : ∀ {T U} → (T ⇒ᴹ U) → (T ⇒ᴹ U) → Set ℓ
    ≈-reflᴹ  : ∀ {T U} {f : T ⇒ᴹ U} → f ≈ᴹ f
    ≈-symᴹ   : ∀ {T U} {f g : T ⇒ᴹ U} → f ≈ᴹ g → g ≈ᴹ f
    ≈-transᴹ : ∀ {T U} {f g h : T ⇒ᴹ U} → f ≈ᴹ g → g ≈ᴹ h → f ≈ᴹ h

    C-congᴹ : ∀ {A B D} {f f′ : B ⇒ᴹ D} {g g′ : A ⇒ᴹ B}
      → f ≈ᴹ f′ → g ≈ᴹ g′ → Cᴹ f g ≈ᴹ Cᴹ f′ g′
    pair-congᴹ : ∀ {A B D} {f f′ : A ⇒ᴹ B} {g g′ : A ⇒ᴹ D}
      → f ≈ᴹ f′ → g ≈ᴹ g′ → pairᴹ f g ≈ᴹ pairᴹ f′ g′
    case-congᴹ : ∀ {A B D} {f f′ : A ⇒ᴹ D} {g g′ : B ⇒ᴹ D}
      → f ≈ᴹ f′ → g ≈ᴹ g′ → caseᴹ f g ≈ᴹ caseᴹ f′ g′
    lam-congᴹ : ∀ {A B D} {f f′ : A `× B ⇒ᴹ D} → f ≈ᴹ f′ → lamᴹ f ≈ᴹ lamᴹ f′
    fmap-congᴹ : ∀ {A B} (G : Ty HO 1) {f f′ : A ⇒ᴹ B}
      → f ≈ᴹ f′ → fmapᴹ G f ≈ᴹ fmapᴹ G f′
    F-congᴹ : ∀ {A B} {G : Ty HO 1}
      {h h′ : (G ⇐ A) `× B ⇒ᴹ A}
      → h ≈ᴹ h′
      → Fᴹ {T = A} {U = B} {G = G} h ≈ᴹ Fᴹ {T = A} {U = B} {G = G} h′

    C-idˡᴹ : ∀ {A B} {f : A ⇒ᴹ B} → Cᴹ idᴹ f ≈ᴹ f
    C-idʳᴹ : ∀ {A B} {f : A ⇒ᴹ B} → Cᴹ f idᴹ ≈ᴹ f
    C-assocᴹ : ∀ {A B D E} {f : D ⇒ᴹ E} {g : B ⇒ᴹ D} {h : A ⇒ᴹ B}
      → Cᴹ f (Cᴹ g h) ≈ᴹ Cᴹ (Cᴹ f g) h

    fmap-idᴹ : ∀ {A} (G : Ty HO 1) → fmapᴹ G (idᴹ {T = A}) ≈ᴹ idᴹ
    fmap-Cᴹ : ∀ {A B D} (G : Ty HO 1) {f : B ⇒ᴹ D} {g : A ⇒ᴹ B}
      → fmapᴹ G (Cᴹ f g) ≈ᴹ Cᴹ (fmapᴹ G f) (fmapᴹ G g)

    strength-naturalˡᴹ : ∀ {A B D} (G : Ty HO 1) {f : A ⇒ᴹ B}
      → Cᴹ (fmapᴹ G (map-×ᴹ structure f (idᴹ {T = D}))) (strengthᴹ {T = A} {U = D} G)
        ≈ᴹ Cᴹ (strengthᴹ {T = B} {U = D} G) (map-×ᴹ structure (fmapᴹ G f) idᴹ)
    strength-naturalʳᴹ : ∀ {A B D} (G : Ty HO 1) {g : B ⇒ᴹ D}
      → Cᴹ (fmapᴹ G (map-×ᴹ structure (idᴹ {T = A}) g)) (strengthᴹ {T = A} {U = B} G)
        ≈ᴹ Cᴹ (strengthᴹ {T = A} {U = D} G) (map-×ᴹ structure idᴹ g)
    strength-π₁ᴹ : ∀ {A B} (G : Ty HO 1)
      → Cᴹ (fmapᴹ G (π₁ᴹ {T = A} {U = B})) (strengthᴹ {T = A} {U = B} G)
        ≈ᴹ π₁ᴹ

    𝟙-uniqueᴹ : ∀ {A} {f : A ⇒ᴹ `𝟙} → f ≈ᴹ ⊤ᴹ
    𝟘-uniqueᴹ : ∀ {A} {f : `𝟘 ⇒ᴹ A} → f ≈ᴹ ⊥ᴹ

    ×-β₁ᴹ : ∀ {A B D} {f : A ⇒ᴹ B} {g : A ⇒ᴹ D} → Cᴹ π₁ᴹ (pairᴹ f g) ≈ᴹ f
    ×-β₂ᴹ : ∀ {A B D} {f : A ⇒ᴹ B} {g : A ⇒ᴹ D} → Cᴹ π₂ᴹ (pairᴹ f g) ≈ᴹ g
    ×-ηᴹ : ∀ {A B D} {f : A ⇒ᴹ B `× D} → pairᴹ (Cᴹ π₁ᴹ f) (Cᴹ π₂ᴹ f) ≈ᴹ f

    +-β₁ᴹ : ∀ {A B D} {f : A ⇒ᴹ D} {g : B ⇒ᴹ D} → Cᴹ (caseᴹ f g) ι₁ᴹ ≈ᴹ f
    +-β₂ᴹ : ∀ {A B D} {f : A ⇒ᴹ D} {g : B ⇒ᴹ D} → Cᴹ (caseᴹ f g) ι₂ᴹ ≈ᴹ g
    +-ηᴹ : ∀ {A B D} {f : A `+ B ⇒ᴹ D} → caseᴹ (Cᴹ f ι₁ᴹ) (Cᴹ f ι₂ᴹ) ≈ᴹ f

    ⇒-βᴹ : ∀ {A B D} {f : A `× B ⇒ᴹ D} → thetaᴹ structure (lamᴹ f) ≈ᴹ f
    ⇒-ηᴹ : ∀ {A B D} {f : A ⇒ᴹ B `⇒ D} → lamᴹ (thetaᴹ structure f) ≈ᴹ f

    F-βᴹ : ∀ {A B} {G : Ty HO 1} {h : (G ⇐ A) `× B ⇒ᴹ A}
      → Cᴹ (Fᴹ {T = A} {U = B} {G = G} h) (map-×ᴹ structure (foldᴹ {G = G}) (idᴹ {T = B}))
        ≈ᴹ Cᴹ h (foldArgsᴹ structure G (Fᴹ {T = A} {U = B} {G = G} h))
    F-uniqueᴹ : ∀ {A B} {G : Ty HO 1} {h : (G ⇐ A) `× B ⇒ᴹ A}
      {p : ind G `× B ⇒ᴹ A}
      → Cᴹ p (map-×ᴹ structure (foldᴹ {G = G}) (idᴹ {T = B})) ≈ᴹ Cᴹ h (foldArgsᴹ structure G p)
      → p ≈ᴹ Fᴹ {T = A} {U = B} {G = G} h

----------------------------------------------------------------------
-- Interpretation and soundness
----------------------------------------------------------------------

module _ {ℓ} (S : Structure ℓ) where
  open Structure S

  interpret : ∀ {T U} → T Syn.→ᶠ U → T ⇒ᴹ U
  interpret Syn.id = idᴹ
  interpret (Syn.C f g) = Cᴹ (interpret f) (interpret g)
  interpret Syn.`⊤ = ⊤ᴹ
  interpret Syn.`⊥ = ⊥ᴹ
  interpret (Syn.`# f g) = pairᴹ (interpret f) (interpret g)
  interpret Syn.π₁ = π₁ᴹ
  interpret Syn.π₂ = π₂ᴹ
  interpret Syn.ι₁ = ι₁ᴹ
  interpret Syn.ι₂ = ι₂ᴹ
  interpret (Syn.`case f g) = caseᴹ (interpret f) (interpret g)
  interpret (Syn.lam f) = lamᴹ (interpret f)
  interpret Syn.apply = applyᴹ
  interpret (Syn.fmap G f) = fmapᴹ G (interpret f)
  interpret (Syn.strength G) = strengthᴹ G
  interpret Syn.fold = foldᴹ
  interpret (Syn.F h) = Fᴹ (interpret h)

module _ {ℓ} (M : Model ℓ) where
  open Model M

  sound : ∀ {T U} {f g : T Syn.→ᶠ U}
    → f Eq.≈ g → interpret structure f ≈ᴹ interpret structure g
  sound Eq.≈-refl = ≈-reflᴹ
  sound (Eq.≈-sym p) = ≈-symᴹ (sound p)
  sound (Eq.≈-trans p q) = ≈-transᴹ (sound p) (sound q)
  sound (Eq.C-cong p q) = C-congᴹ (sound p) (sound q)
  sound (Eq.`#-cong p q) = pair-congᴹ (sound p) (sound q)
  sound (Eq.`case-cong p q) = case-congᴹ (sound p) (sound q)
  sound (Eq.lam-cong p) = lam-congᴹ (sound p)
  sound (Eq.fmap-cong G p) = fmap-congᴹ G (sound p)
  sound (Eq.F-cong {A = A} {B = B} {H = H} p) = F-congᴹ {A = A} {B = B} {G = H} (sound p)
  sound Eq.C-idˡ = C-idˡᴹ
  sound Eq.C-idʳ = C-idʳᴹ
  sound Eq.C-assoc = C-assocᴹ
  sound (Eq.fmap-id G) = fmap-idᴹ G
  sound (Eq.fmap-C G) = fmap-Cᴹ G
  sound (Eq.strength-naturalˡ G) = strength-naturalˡᴹ G
  sound (Eq.strength-naturalʳ G) = strength-naturalʳᴹ G
  sound (Eq.strength-π₁ G) = strength-π₁ᴹ G
  sound Eq.𝟙-unique = 𝟙-uniqueᴹ
  sound Eq.𝟘-unique = 𝟘-uniqueᴹ
  sound Eq.×-β₁ = ×-β₁ᴹ
  sound Eq.×-β₂ = ×-β₂ᴹ
  sound Eq.×-η = ×-ηᴹ
  sound Eq.+-β₁ = +-β₁ᴹ
  sound Eq.+-β₂ = +-β₂ᴹ
  sound Eq.+-η = +-ηᴹ
  sound Eq.⇒-β = ⇒-βᴹ
  sound Eq.⇒-η = ⇒-ηᴹ
  sound Eq.F-β = F-βᴹ
  sound (Eq.F-unique p) = F-uniqueᴹ (sound p)
