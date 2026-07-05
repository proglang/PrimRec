{-# OPTIONS --safe #-}

module Core.Translations.PRFOParamorphismFold where

import Core.PRFO as P
import Core.PRFOFold as F
import Core.Equations.PRFO as PEq
import Core.Equations.PRFOFold as FEq
open import Core.Types

variable
  W : TY FO

----------------------------------------------------------------------
-- Derived eliminators
----------------------------------------------------------------------

-- Catamorphism in the paramorphism-primitive presentation: drop the
-- remembered original subterm from the paramorphism layer.
module _ where
  --! CorePRFOParamorphismFoldDerivedP {
  open import Core.PRFO

  dropSubtermᴾ : ∀ {T U} (G : Ty FO 1) →
    (G [ T ]) `× U →ᴾ T →
    (G [ T `× ind G ]) `× U →ᴾ T
  dropSubtermᴾ G h =
    C h (`# (C (fmap G π₁) π₁) π₂)

  Fᴾ : ∀ {T U} {G : Ty FO 1} →
    (G [ T ]) `× U →ᴾ T →
    ind G `× U →ᴾ T
  Fᴾ {G = G} h = P (dropSubtermᴾ G h)
  --! }

-- Paramorphism in the catamorphism-primitive presentation: construct pairs
-- consisting of the recursive result and the original reconstructed subterm.
module _ where
  --! CorePRFOParamorphismFoldDerivedF {
  open import Core.PRFOFold

  rebuildᶠ : ∀ {T U} (G : Ty FO 1) →
    (G [ T `× ind G ]) `× U →ᶠ ind G
  rebuildᶠ G =
    C con (C (fmap G π₂) π₁)

  rememberᶠ : ∀ {T U} (G : Ty FO 1) →
    (G [ T `× ind G ]) `× U →ᶠ T →
    (G [ T `× ind G ]) `× U →ᶠ T `× ind G
  rememberᶠ G h = `# h (rebuildᶠ G)

  Pᶠ : ∀ {T U} {G : Ty FO 1} →
    (G [ T `× ind G ]) `× U →ᶠ T →
    ind G `× U →ᶠ T
  Pᶠ {G = G} h = C π₁ (F (rememberᶠ G h))
  --! }

----------------------------------------------------------------------
-- Raw translations
----------------------------------------------------------------------

toP : ∀ {T U} → T F.→ᶠ U → T P.→ᴾ U
toP F.id = P.id
toP (F.C f g) = P.C (toP f) (toP g)
toP F.`⊤ = P.`⊤
toP F.`⊥ = P.`⊥
toP (F.`# f g) = P.`# (toP f) (toP g)
toP F.π₁ = P.π₁
toP F.π₂ = P.π₂
toP F.ι₁ = P.ι₁
toP F.ι₂ = P.ι₂
toP (F.`case f g) = P.`case (toP f) (toP g)
toP F.dist-+-× = P.dist-+-×
toP (F.fmap G f) = P.fmap G (toP f)
toP (F.strength G) = P.strength G
toP F.con = P.con
toP (F.F {G = G} h) = Fᴾ (toP h)

toF : ∀ {T U} → T P.→ᴾ U → T F.→ᶠ U
toF P.id = F.id
toF (P.C f g) = F.C (toF f) (toF g)
toF P.`⊤ = F.`⊤
toF P.`⊥ = F.`⊥
toF (P.`# f g) = F.`# (toF f) (toF g)
toF P.π₁ = F.π₁
toF P.π₂ = F.π₂
toF P.ι₁ = F.ι₁
toF P.ι₂ = F.ι₂
toF (P.`case f g) = F.`case (toF f) (toF g)
toF P.dist-+-× = F.dist-+-×
toF (P.fmap G f) = F.fmap G (toF f)
toF (P.strength G) = F.strength G
toF P.con = F.con
toF {T = ind G `× U} {U = T} (P.P h) = Pᶠ (toF h)

----------------------------------------------------------------------
-- Equation preservation: fold-primitive into paramorphism-primitive
----------------------------------------------------------------------

foldArgsᴾ : (G : Ty FO 1) → (P.ind G P.`× U P.→ᴾ T)
  → (G [ P.ind G ]) P.`× U P.→ᴾ (G [ T ]) P.`× U
foldArgsᴾ G p = P.`# (P.pmap G p) P.π₂

dropLayerᴾ : ∀ {T} (G : Ty FO 1) {U : TY FO} →
  (G [ T P.`× P.ind G ]) P.`× U P.→ᴾ (G [ T ]) P.`× U
dropLayerᴾ G = P.`# (P.C (P.fmap G P.π₁) P.π₁) P.π₂

C-#ᴾ : ∀ {A B D E : TY FO}
  {f : B P.→ᴾ D} {g : B P.→ᴾ E} {h : A P.→ᴾ B} →
  P.C (P.`# f g) h PEq.≈ P.`# (P.C f h) (P.C g h)
C-#ᴾ =
  PEq.≈-trans (PEq.≈-sym PEq.×-η)
    (PEq.`#-cong
      (PEq.≈-trans PEq.C-assoc (PEq.C-cong PEq.×-β₁ PEq.≈-refl))
      (PEq.≈-trans PEq.C-assoc (PEq.C-cong PEq.×-β₂ PEq.≈-refl)))

map-×-congᴾ : ∀ {A B D E : TY FO}
  {f f′ : A P.→ᴾ D} {g g′ : B P.→ᴾ E} →
  f PEq.≈ f′ → g PEq.≈ g′ → P.map-× f g PEq.≈ P.map-× f′ g′
map-×-congᴾ f≈ g≈ =
  PEq.`#-cong (PEq.C-cong f≈ PEq.≈-refl) (PEq.C-cong g≈ PEq.≈-refl)

drop-first-paraArgsᴾ : ∀ {T U} (G : Ty FO 1)
  (p : P.ind G P.`× U P.→ᴾ T) →
  P.C (P.C (P.fmap G P.π₁) P.π₁) (P.paraArgs G p)
  PEq.≈ P.pmap G p
drop-first-paraArgsᴾ G p =
  PEq.≈-trans (PEq.≈-sym PEq.C-assoc)
    (PEq.≈-trans
      (PEq.C-cong PEq.≈-refl PEq.×-β₁)
      (PEq.≈-trans PEq.C-assoc
        (PEq.C-cong
          (PEq.≈-trans
            (PEq.≈-sym (PEq.fmap-C G))
            (PEq.fmap-cong G PEq.×-β₁))
          PEq.≈-refl)))

dropLayer-paraArgsᴾ : ∀ {T U} (G : Ty FO 1)
  (p : P.ind G P.`× U P.→ᴾ T) →
  P.C (dropLayerᴾ G) (P.paraArgs G p) PEq.≈ foldArgsᴾ G p
dropLayer-paraArgsᴾ G p =
  PEq.≈-trans C-#ᴾ
    (PEq.`#-cong (drop-first-paraArgsᴾ G p) PEq.×-β₂)

dropSubterm-paraArgsᴾ : ∀ {T U} (G : Ty FO 1)
  (h : (G [ T ]) P.`× U P.→ᴾ T)
  (p : P.ind G P.`× U P.→ᴾ T) →
  P.C (dropSubtermᴾ G h) (P.paraArgs G p)
  PEq.≈ P.C h (foldArgsᴾ G p)
dropSubterm-paraArgsᴾ G h p =
  PEq.≈-trans (PEq.≈-sym PEq.C-assoc)
    (PEq.C-cong PEq.≈-refl (dropLayer-paraArgsᴾ G p))

Fᴾ-β : ∀ {T U} {G : Ty FO 1}
  {h : (G [ T ]) P.`× U P.→ᴾ T} →
  P.C (Fᴾ {G = G} h) (P.map-× (P.con {G = G}) (P.id {T = U}))
  PEq.≈
  P.C h (foldArgsᴾ G (Fᴾ {G = G} h))
Fᴾ-β {G = G} {h = h} =
  PEq.≈-trans PEq.P-β
    (dropSubterm-paraArgsᴾ G h (Fᴾ h))

Fᴾ-unique : ∀ {T U} {G : Ty FO 1}
  {h : (G [ T ]) P.`× U P.→ᴾ T}
  {p : P.ind G P.`× U P.→ᴾ T} →
  P.C p (P.map-× (P.con {G = G}) (P.id {T = U}))
  PEq.≈ P.C h (foldArgsᴾ G p) →
  p PEq.≈ Fᴾ {G = G} h
Fᴾ-unique {G = G} {h = h} premise =
  PEq.P-unique
    (PEq.≈-trans premise
      (PEq.≈-sym (dropSubterm-paraArgsᴾ G h _)))

toP-preserves : ∀ {T U} {f g : T F.→ᶠ U} →
  f FEq.≈ g → toP f PEq.≈ toP g
toP-preserves FEq.≈-refl = PEq.≈-refl
toP-preserves (FEq.≈-sym p) = PEq.≈-sym (toP-preserves p)
toP-preserves (FEq.≈-trans p q) =
  PEq.≈-trans (toP-preserves p) (toP-preserves q)
toP-preserves (FEq.C-cong p q) =
  PEq.C-cong (toP-preserves p) (toP-preserves q)
toP-preserves (FEq.`#-cong p q) =
  PEq.`#-cong (toP-preserves p) (toP-preserves q)
toP-preserves (FEq.`case-cong p q) =
  PEq.`case-cong (toP-preserves p) (toP-preserves q)
toP-preserves (FEq.fmap-cong G p) =
  PEq.fmap-cong G (toP-preserves p)
toP-preserves (FEq.F-cong {H = H} p) =
  PEq.P-cong (PEq.C-cong (toP-preserves p) PEq.≈-refl)
toP-preserves FEq.C-idˡ = PEq.C-idˡ
toP-preserves FEq.C-idʳ = PEq.C-idʳ
toP-preserves FEq.C-assoc = PEq.C-assoc
toP-preserves (FEq.fmap-id G) = PEq.fmap-id G
toP-preserves (FEq.fmap-C G) = PEq.fmap-C G
toP-preserves (FEq.strength-naturalˡ G) = PEq.strength-naturalˡ G
toP-preserves (FEq.strength-naturalʳ G) = PEq.strength-naturalʳ G
toP-preserves (FEq.strength-π₁ G) = PEq.strength-π₁ G
toP-preserves FEq.𝟙-unique = PEq.𝟙-unique
toP-preserves FEq.𝟘-unique = PEq.𝟘-unique
toP-preserves FEq.×-β₁ = PEq.×-β₁
toP-preserves FEq.×-β₂ = PEq.×-β₂
toP-preserves FEq.×-η = PEq.×-η
toP-preserves FEq.+-β₁ = PEq.+-β₁
toP-preserves FEq.+-β₂ = PEq.+-β₂
toP-preserves FEq.+-η = PEq.+-η
toP-preserves FEq.dist-undist = PEq.dist-undist
toP-preserves FEq.undist-dist = PEq.undist-dist
toP-preserves (FEq.F-β {H = H} {h = h}) =
  Fᴾ-β {G = H} {h = toP h}
toP-preserves (FEq.F-unique p) =
  Fᴾ-unique (toP-preserves p)

----------------------------------------------------------------------
-- Equation preservation: paramorphism-primitive into fold-primitive
----------------------------------------------------------------------

paraArgsᶠ : (G : Ty FO 1) → (F.ind G F.`× U F.→ᶠ T)
  → (G [ F.ind G ]) F.`× U F.→ᶠ (G [ T F.`× F.ind G ]) F.`× U
paraArgsᶠ G p = F.`# (F.pmap G (F.`# p F.π₁)) F.π₂

rebuild₀ᶠ : ∀ {U} (G : Ty FO 1) →
  (G [ F.ind G ]) F.`× U F.→ᶠ F.ind G
rebuild₀ᶠ G = F.C F.con F.π₁

C-#ᶠ : ∀ {A B D E : TY FO}
  {f : B F.→ᶠ D} {g : B F.→ᶠ E} {h : A F.→ᶠ B} →
  F.C (F.`# f g) h FEq.≈ F.`# (F.C f h) (F.C g h)
C-#ᶠ =
  FEq.≈-trans (FEq.≈-sym FEq.×-η)
    (FEq.`#-cong
      (FEq.≈-trans FEq.C-assoc (FEq.C-cong FEq.×-β₁ FEq.≈-refl))
      (FEq.≈-trans FEq.C-assoc (FEq.C-cong FEq.×-β₂ FEq.≈-refl)))

pmap-congᶠ : ∀ {A B U : TY FO} (G : Ty FO 1)
  {f f′ : A F.`× U F.→ᶠ B} →
  f FEq.≈ f′ → F.pmap G f FEq.≈ F.pmap G f′
pmap-congᶠ G f≈ =
  FEq.C-cong (FEq.fmap-cong G f≈) FEq.≈-refl

foldArgs-congᶠ : ∀ {T U} (G : Ty FO 1)
  {p p′ : F.ind G F.`× U F.→ᶠ T} →
  p FEq.≈ p′ → F.foldArgs G p FEq.≈ F.foldArgs G p′
foldArgs-congᶠ G p≈ =
  FEq.`#-cong (pmap-congᶠ G p≈) FEq.≈-refl

pmap-Cᶠ : ∀ {A B D U : TY FO} (G : Ty FO 1)
  {f : B F.→ᶠ D} {g : A F.`× U F.→ᶠ B} →
  F.C (F.fmap G f) (F.pmap G g) FEq.≈ F.pmap G (F.C f g)
pmap-Cᶠ G =
  FEq.≈-trans FEq.C-assoc
    (FEq.C-cong (FEq.≈-sym (FEq.fmap-C G)) FEq.≈-refl)

π₁-con-mapᶠ : ∀ {U} {G : Ty FO 1} →
  F.C F.π₁ (F.map-× (F.con {G = G}) (F.id {T = U}))
  FEq.≈ F.C F.con F.π₁
π₁-con-mapᶠ = FEq.×-β₁

rebuild₀-foldArgs-π₁ᶠ : ∀ {U} (G : Ty FO 1) →
  F.C (rebuild₀ᶠ {U = U} G) (F.foldArgs G F.π₁)
  FEq.≈ F.C F.con F.π₁
rebuild₀-foldArgs-π₁ᶠ G =
  FEq.≈-trans (FEq.≈-sym FEq.C-assoc)
    (FEq.≈-trans
      (FEq.C-cong FEq.≈-refl FEq.×-β₁)
      (FEq.C-cong FEq.≈-refl (FEq.strength-π₁ G)))

π₁-is-F-rebuild₀ᶠ : ∀ {U} (G : Ty FO 1) →
  F.π₁ FEq.≈ F.F {G = G} {T = F.ind G} {U = U} (rebuild₀ᶠ G)
π₁-is-F-rebuild₀ᶠ {U = U} G =
  FEq.F-unique
    (FEq.≈-trans π₁-con-mapᶠ
      (FEq.≈-sym (rebuild₀-foldArgs-π₁ᶠ {U = U} G)))

rebuild-foldArgsᶠ : ∀ {T U} (G : Ty FO 1)
  (r : F.ind G F.`× U F.→ᶠ T F.`× F.ind G) →
  F.C (rebuildᶠ G) (F.foldArgs G r)
  FEq.≈
  F.C (rebuild₀ᶠ G) (F.foldArgs G (F.C F.π₂ r))
rebuild-foldArgsᶠ G r =
  FEq.≈-trans (FEq.≈-sym FEq.C-assoc)
    (FEq.≈-trans
      (FEq.C-cong FEq.≈-refl (FEq.≈-sym FEq.C-assoc))
      (FEq.≈-trans
        (FEq.C-cong FEq.≈-refl
          (FEq.C-cong FEq.≈-refl FEq.×-β₁))
        (FEq.≈-trans
          (FEq.C-cong FEq.≈-refl (pmap-Cᶠ G))
          (FEq.≈-trans
            (FEq.C-cong FEq.≈-refl (FEq.≈-sym FEq.×-β₁))
            FEq.C-assoc))))

second-is-F-rebuild₀ᶠ : ∀ {T U} {G : Ty FO 1}
  (h : (G [ T F.`× F.ind G ]) F.`× U F.→ᶠ T) →
  F.C F.π₂ (F.F (rememberᶠ G h))
  FEq.≈ F.F {G = G} {T = F.ind G} {U = U} (rebuild₀ᶠ G)
second-is-F-rebuild₀ᶠ {G = G} h =
  FEq.F-unique
    (FEq.≈-trans (FEq.≈-sym FEq.C-assoc)
      (FEq.≈-trans
        (FEq.C-cong FEq.≈-refl FEq.F-β)
        (FEq.≈-trans FEq.C-assoc
          (FEq.≈-trans
            (FEq.C-cong FEq.×-β₂ FEq.≈-refl)
            (rebuild-foldArgsᶠ G (F.F (rememberᶠ G h)))))))

remember-secondᶠ : ∀ {T U} {G : Ty FO 1}
  (h : (G [ T F.`× F.ind G ]) F.`× U F.→ᶠ T) →
  F.C F.π₂ (F.F (rememberᶠ G h)) FEq.≈ F.π₁
remember-secondᶠ {G = G} h =
  FEq.≈-trans (second-is-F-rebuild₀ᶠ h)
    (FEq.≈-sym (π₁-is-F-rebuild₀ᶠ G))

remember-ηᶠ : ∀ {T U} {G : Ty FO 1}
  (h : (G [ T F.`× F.ind G ]) F.`× U F.→ᶠ T) →
  F.F (rememberᶠ G h) FEq.≈ F.`# (Pᶠ h) F.π₁
remember-ηᶠ h =
  FEq.≈-trans (FEq.≈-sym FEq.×-η)
    (FEq.`#-cong FEq.≈-refl (remember-secondᶠ h))

foldArgs-rememberᶠ : ∀ {T U} {G : Ty FO 1}
  (h : (G [ T F.`× F.ind G ]) F.`× U F.→ᶠ T) →
  F.foldArgs G (F.F (rememberᶠ G h)) FEq.≈ paraArgsᶠ G (Pᶠ h)
foldArgs-rememberᶠ {G = G} h =
  foldArgs-congᶠ G (remember-ηᶠ h)

Pᶠ-β : ∀ {T U} {G : Ty FO 1}
  {h : (G [ T F.`× F.ind G ]) F.`× U F.→ᶠ T} →
  F.C (Pᶠ {G = G} h) (F.map-× (F.con {G = G}) (F.id {T = U}))
  FEq.≈
  F.C h (paraArgsᶠ G (Pᶠ {G = G} h))
Pᶠ-β {G = G} {h = h} =
  FEq.≈-trans (FEq.≈-sym FEq.C-assoc)
    (FEq.≈-trans
      (FEq.C-cong FEq.≈-refl FEq.F-β)
      (FEq.≈-trans FEq.C-assoc
        (FEq.≈-trans
          (FEq.C-cong FEq.×-β₁ FEq.≈-refl)
          (FEq.C-cong FEq.≈-refl (foldArgs-rememberᶠ h)))))

rebuild-paraArgsᶠ : ∀ {T U} (G : Ty FO 1)
  (p : F.ind G F.`× U F.→ᶠ T) →
  F.C (rebuildᶠ G) (paraArgsᶠ G p) FEq.≈ F.C F.con F.π₁
rebuild-paraArgsᶠ G p =
  FEq.≈-trans (rebuild-foldArgsᶠ G (F.`# p F.π₁))
    (FEq.≈-trans
      (FEq.C-cong FEq.≈-refl
        (foldArgs-congᶠ G FEq.×-β₂))
      (rebuild₀-foldArgs-π₁ᶠ G))

Pᶠ-unique : ∀ {T U} {G : Ty FO 1}
  {h : (G [ T F.`× F.ind G ]) F.`× U F.→ᶠ T}
  {p : F.ind G F.`× U F.→ᶠ T} →
  F.C p (F.map-× (F.con {G = G}) (F.id {T = U}))
  FEq.≈ F.C h (paraArgsᶠ G p) →
  p FEq.≈ Pᶠ {G = G} h
Pᶠ-unique {G = G} {h = h} {p = p} premise =
  FEq.≈-trans (FEq.≈-sym FEq.×-β₁)
    (FEq.C-cong FEq.≈-refl
      (FEq.F-unique
        (FEq.≈-trans C-#ᶠ
          (FEq.≈-trans
            (FEq.`#-cong premise
              (FEq.≈-trans π₁-con-mapᶠ
                (FEq.≈-sym (rebuild-paraArgsᶠ G p))))
            (FEq.≈-sym C-#ᶠ)))))

toF-preserves : ∀ {T U} {f g : T P.→ᴾ U} →
  f PEq.≈ g → toF f FEq.≈ toF g
toF-preserves PEq.≈-refl = FEq.≈-refl
toF-preserves (PEq.≈-sym p) = FEq.≈-sym (toF-preserves p)
toF-preserves (PEq.≈-trans p q) =
  FEq.≈-trans (toF-preserves p) (toF-preserves q)
toF-preserves (PEq.C-cong p q) =
  FEq.C-cong (toF-preserves p) (toF-preserves q)
toF-preserves (PEq.`#-cong p q) =
  FEq.`#-cong (toF-preserves p) (toF-preserves q)
toF-preserves (PEq.`case-cong p q) =
  FEq.`case-cong (toF-preserves p) (toF-preserves q)
toF-preserves (PEq.fmap-cong G p) =
  FEq.fmap-cong G (toF-preserves p)
toF-preserves (PEq.P-cong {G = H} p) =
  FEq.C-cong FEq.≈-refl
    (FEq.F-cong (FEq.`#-cong (toF-preserves p) FEq.≈-refl))
toF-preserves PEq.C-idˡ = FEq.C-idˡ
toF-preserves PEq.C-idʳ = FEq.C-idʳ
toF-preserves PEq.C-assoc = FEq.C-assoc
toF-preserves (PEq.fmap-id G) = FEq.fmap-id G
toF-preserves (PEq.fmap-C G) = FEq.fmap-C G
toF-preserves (PEq.strength-naturalˡ G) = FEq.strength-naturalˡ G
toF-preserves (PEq.strength-naturalʳ G) = FEq.strength-naturalʳ G
toF-preserves (PEq.strength-π₁ G) = FEq.strength-π₁ G
toF-preserves PEq.𝟙-unique = FEq.𝟙-unique
toF-preserves PEq.𝟘-unique = FEq.𝟘-unique
toF-preserves PEq.×-β₁ = FEq.×-β₁
toF-preserves PEq.×-β₂ = FEq.×-β₂
toF-preserves PEq.×-η = FEq.×-η
toF-preserves PEq.+-β₁ = FEq.+-β₁
toF-preserves PEq.+-β₂ = FEq.+-β₂
toF-preserves PEq.+-η = FEq.+-η
toF-preserves PEq.dist-undist = FEq.dist-undist
toF-preserves PEq.undist-dist = FEq.undist-dist
toF-preserves (PEq.P-β {G = H} {h = h}) =
  Pᶠ-β {G = H} {h = toF h}
toF-preserves (PEq.P-unique p) =
  Pᶠ-unique (toF-preserves p)

----------------------------------------------------------------------
-- Round trips up to the respective equational theories
----------------------------------------------------------------------

toP-toF : ∀ {T U} (f : T P.→ᴾ U) → toP (toF f) PEq.≈ f
toP-toF P.id = PEq.≈-refl
toP-toF (P.C f g) = PEq.C-cong (toP-toF f) (toP-toF g)
toP-toF P.`⊤ = PEq.≈-refl
toP-toF P.`⊥ = PEq.≈-refl
toP-toF (P.`# f g) = PEq.`#-cong (toP-toF f) (toP-toF g)
toP-toF P.π₁ = PEq.≈-refl
toP-toF P.π₂ = PEq.≈-refl
toP-toF P.ι₁ = PEq.≈-refl
toP-toF P.ι₂ = PEq.≈-refl
toP-toF (P.`case f g) = PEq.`case-cong (toP-toF f) (toP-toF g)
toP-toF P.dist-+-× = PEq.≈-refl
toP-toF (P.fmap G f) = PEq.fmap-cong G (toP-toF f)
toP-toF (P.strength G) = PEq.≈-refl
toP-toF P.con = PEq.≈-refl
toP-toF {T = ind G `× U} {U = T} (P.P h) =
  PEq.P-unique
    (PEq.≈-trans
      (toP-preserves (Pᶠ-β {G = G} {h = toF h}))
      (PEq.C-cong (toP-toF h) PEq.≈-refl))

toF-toP : ∀ {T U} (f : T F.→ᶠ U) → toF (toP f) FEq.≈ f
toF-toP F.id = FEq.≈-refl
toF-toP (F.C f g) = FEq.C-cong (toF-toP f) (toF-toP g)
toF-toP F.`⊤ = FEq.≈-refl
toF-toP F.`⊥ = FEq.≈-refl
toF-toP (F.`# f g) = FEq.`#-cong (toF-toP f) (toF-toP g)
toF-toP F.π₁ = FEq.≈-refl
toF-toP F.π₂ = FEq.≈-refl
toF-toP F.ι₁ = FEq.≈-refl
toF-toP F.ι₂ = FEq.≈-refl
toF-toP (F.`case f g) = FEq.`case-cong (toF-toP f) (toF-toP g)
toF-toP F.dist-+-× = FEq.≈-refl
toF-toP (F.fmap G f) = FEq.fmap-cong G (toF-toP f)
toF-toP (F.strength G) = FEq.≈-refl
toF-toP F.con = FEq.≈-refl
toF-toP (F.F {G = G} h) =
  FEq.F-unique
    (FEq.≈-trans
      (toF-preserves (Fᴾ-β {G = G} {h = toP h}))
      (FEq.C-cong (toF-toP h) FEq.≈-refl))

----------------------------------------------------------------------
-- Compact theorem statements used in the paper
----------------------------------------------------------------------

module _ where
  --! CorePRFOParamorphismFoldLawsP {
  open import Core.Equations.PRFO

  Fᴾ-β′ : ∀ {T U} {G : Ty FO 1}
    {h : (G [ T ]) `× U →ᴾ T} →
    C (Fᴾ h) (map-× (con {G = G}) id) ≈ C h (foldArgsᴾ G (Fᴾ h))
  --! [
  Fᴾ-β′ = Fᴾ-β
  --! ]
  Fᴾ-unique′ : ∀ {T U} {G : Ty FO 1}
    {h : (G [ T ]) `× U →ᴾ T} {p : ind G `× U →ᴾ T} →
    C p (map-× (con {G = G}) id) ≈ C h (foldArgsᴾ G p) →
    p ≈ Fᴾ h
  --! [
  Fᴾ-unique′ = Fᴾ-unique
  --! ]
  --! }

module _ where
  --! CorePRFOParamorphismFoldLawsF {
  open import Core.Equations.PRFOFold

  Pᶠ-β′ : ∀ {T U} {G : Ty FO 1}
    {h : (G [ T `× ind G ]) `× U →ᶠ T} →
    C (Pᶠ h) (map-× (con {G = G}) id) ≈ C h (paraArgsᶠ G (Pᶠ h))
  --! [
  Pᶠ-β′ = Pᶠ-β
  --! ]
  Pᶠ-unique′ : ∀ {T U} {G : Ty FO 1}
    {h : (G [ T `× ind G ]) `× U →ᶠ T} {p : ind G `× U →ᶠ T} →
    C p (map-× (con {G = G}) id) ≈ C h (paraArgsᶠ G p) →
    p ≈ Pᶠ h
  --! [
  Pᶠ-unique′ = Pᶠ-unique
  --! ]
  --! }

module _ where
  --! CorePRFOParamorphismFoldEquivalence {
  open import Core.Equations.PRFO as PEq
  open import Core.Equations.PRFOFold as FEq

  toP-preserves′ : ∀ {T U} {f g : T F.→ᶠ U} →
    f FEq.≈ g → toP f PEq.≈ toP g
  --! [
  toP-preserves′ = toP-preserves
  --! ]
  toF-preserves′ : ∀ {T U} {f g : T P.→ᴾ U} →
    f PEq.≈ g → toF f FEq.≈ toF g
  --! [
  toF-preserves′ = toF-preserves
  --! ]
  toP-toF′ : ∀ {T U} (f : T P.→ᴾ U) → toP (toF f) PEq.≈ f
  --! [
  toP-toF′ = toP-toF
  --! ]
  toF-toP′ : ∀ {T U} (f : T F.→ᶠ U) → toF (toP f) FEq.≈ f
  --! [
  toF-toP′ = toF-toP
  --! ]
  --! }
