{-# OPTIONS --safe #-}

module Core.Instances.Concrete.Evaluator where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Core.PRFO
open import Core.Semantics.Containers
open import Core.Semantics.Inductive
open import Core.Semantics.Types

----------------------------------------------------------------------
-- Flat unary polynomial generators
----------------------------------------------------------------------

data Flat : Ty FO 1 → Set where
  flat-𝟘 : Flat `𝟘
  flat-𝟙 : Flat `𝟙
  flat-` : Flat (` zero)
  flat-× : ∀ {G H} → Flat G → Flat H → Flat (G `× H)
  flat-+ : ∀ {G H} → Flat G → Flat H → Flat (G `+ H)

Sem : TY FO → Set
Sem = ⟦_⟧₀

-- Convert between syntactic substitution and a container extension.  These
-- functions are total because Flat excludes nested ind and exponentials.
pack : ∀ {G} → Flat G → (T : TY FO) →
       Sem (G [ T ]) → Value (code G) (λ _ → Sem T)
pack flat-𝟘 T ()
pack flat-𝟙 T tt = tt , λ _ ()
pack flat-` T x = tt , λ { zero refl → x }
pack (flat-× p q) T (x , y) with pack p T x | pack q T y
... | sx , vx | sy , vy =
  (sx , sy) , λ
    { i (inj₁ r) → vx i r
    ; i (inj₂ r) → vy i r
    }
pack (flat-+ p q) T (inj₁ x) with pack p T x
... | sx , vx = inj₁ sx , vx
pack (flat-+ p q) T (inj₂ y) with pack q T y
... | sy , vy = inj₂ sy , vy

unpack : ∀ {G} → Flat G → (T : TY FO) →
         Value (code G) (λ _ → Sem T) → Sem (G [ T ])
unpack flat-𝟘 T (() , values)
unpack flat-𝟙 T (tt , values) = tt
unpack flat-` T (tt , values) = values zero refl
unpack (flat-× p q) T ((sx , sy) , values) =
  unpack p T (sx , λ i r → values i (inj₁ r)) ,
  unpack q T (sy , λ i r → values i (inj₂ r))
unpack (flat-+ p q) T (inj₁ sx , values) = inj₁ (unpack p T (sx , values))
unpack (flat-+ p q) T (inj₂ sy , values) = inj₂ (unpack q T (sy , values))

unpack-cong : ∀ {G} (p : Flat G) (T : TY FO) {s : Shape (code G)}
  {xs ys : (i : Fin 1) → Position (code G) s i → Sem T} →
  ((i : Fin 1) (position : Position (code G) s i) →
    xs i position ≡ ys i position) →
  unpack p T (s , xs) ≡ unpack p T (s , ys)
unpack-cong flat-𝟘 T {s = ()} pointwise
unpack-cong flat-𝟙 T pointwise = refl
unpack-cong flat-` T pointwise = pointwise zero refl
unpack-cong (flat-× p q) T {s = sx , sy} pointwise =
  cong₂ _,_
    (unpack-cong p T (λ i position → pointwise i (inj₁ position)))
    (unpack-cong q T (λ i position → pointwise i (inj₂ position)))
unpack-cong (flat-+ p q) T {s = inj₁ sx} pointwise =
  cong inj₁ (unpack-cong p T pointwise)
unpack-cong (flat-+ p q) T {s = inj₂ sy} pointwise =
  cong inj₂ (unpack-cong q T pointwise)

fmapFlat : ∀ {G T U} → Flat G → (Sem T → Sem U) →
           Sem (G [ T ]) → Sem (G [ U ])
fmapFlat {T = T} {U = U} p f x = unpack p U (mapC (λ _ → f) (pack p T x))

strengthFlat : ∀ {G T U} → Flat G →
               Sem ((G [ T ]) `× U) → Sem (G [ T `× U ])
strengthFlat {T = T} {U = U} p (x , u) =
  unpack p (T `× U) (mapC (λ _ t → t , u) (pack p T x))

rollFlat : ∀ {G} → Flat G → Sem (G [ ind G ]) → Sem (ind G)
rollFlat {G} p layer with pack p (ind G) layer
... | s , values =
  proj₁
    (rollC {D = code G} {ρ = λ ()}
      (s , λ { zero position → values zero position , λ () }))

paraAlgebra : ∀ {G T U} → Flat G →
  (Sem ((G [ T `× ind G ]) `× U) → Sem T) → Sem U →
  Value (code G) (extend (Sem T × Mu (code G) (λ ())) (λ ())) → Sem T
paraAlgebra {G} {T} p h u layer =
  h (unpack p (T `× ind G) (mapC strip layer) , u)
  where
  strip : (i : Fin 1) →
    extend (Sem T × Mu (code G) (λ ())) (λ ()) i → Sem (T `× ind G)
  strip zero (result , child) = result , proj₁ child

paraFlat : ∀ {G T U} → Flat G →
  (Sem ((G [ T `× ind G ]) `× U) → Sem T) →
  Sem (ind G `× U) → Sem T
paraFlat {G} {T} {U} p h (tree , u) =
  paraGo (paraAlgebra {G = G} {T = T} {U = U} p h u) tree (λ ())

paraStepFlat : ∀ {G T U} → Flat G →
  (Sem ((G [ T `× ind G ]) `× U) → Sem T) → Sem U →
  Sem (G [ ind G ]) → Sem (G [ T `× ind G ])
paraStepFlat {G} {T} {U} p h u layer =
  unpack p (T `× ind G) (mapC step (pack p (ind G) layer))
  where
  step : (i : Fin 1) → Sem (ind G) → Sem (T `× ind G)
  step zero child = paraFlat {G = G} {T = T} {U = U} p h (child , u) , child

paraStep-as-fmap : ∀ {G T U} (p : Flat G)
  (h : Sem ((G [ T `× ind G ]) `× U) → Sem T)
  (u : Sem U) (layer : Sem (G [ ind G ])) →
  paraStepFlat {G = G} {T = T} {U = U} p h u layer ≡
  fmapFlat {G = G} {T = ind G} {U = T `× ind G} p
    (λ child → paraFlat {G = G} {T = T} {U = U} p h (child , u) , child)
    layer
paraStep-as-fmap {G = G} {T = T} p h u layer =
  unpack-cong p (T `× ind G) λ { zero position → refl }

para-rollFlat-β : ∀ {G T U} (p : Flat G)
  (h : Sem ((G [ T `× ind G ]) `× U) → Sem T)
  (layer : Sem (G [ ind G ])) (u : Sem U) →
  paraFlat {G = G} {T = T} {U = U} p h (rollFlat p layer , u) ≡
  h (paraStepFlat {G = G} {T = T} {U = U} p h u layer , u)
para-rollFlat-β {G = G} {T = T} p h layer u
  with pack p (ind G) layer
... | s , values =
  cong h (cong₂ _,_
    (unpack-cong p (T `× ind G) λ { zero position → refl })
    refl)

----------------------------------------------------------------------
-- Evidence that a Core arrow stays in the executable flat fragment
----------------------------------------------------------------------

data Supported : ∀ {T U} → T →ᴾ U → Set where
  s-id : ∀ {T} → Supported (id {T = T})
  s-C : ∀ {T U V} {f : U →ᴾ V} {g : T →ᴾ U} →
        Supported f → Supported g → Supported (C f g)
  s-⊤ : ∀ {T} → Supported (`⊤ {T = T})
  s-⊥ : ∀ {T} → Supported (`⊥ {T = T})
  s-# : ∀ {T U V} {f : T →ᴾ U} {g : T →ᴾ V} →
        Supported f → Supported g → Supported (`# f g)
  s-π₁ : ∀ {T U} → Supported (π₁ {U = T} {V = U})
  s-π₂ : ∀ {T U} → Supported (π₂ {U = T} {V = U})
  s-ι₁ : ∀ {T U} → Supported (ι₁ {U = T} {V = U})
  s-ι₂ : ∀ {T U} → Supported (ι₂ {V = U} {U = T})
  s-case : ∀ {T U V} {f : T →ᴾ V} {g : U →ᴾ V} →
           Supported f → Supported g → Supported (`case f g)
  s-dist : ∀ {T U V} → Supported (dist-+-× {U = T} {V = U} {T = V})
  s-fmap : ∀ {G T U} {f : T →ᴾ U} →
           Flat G → Supported f → Supported (fmap G f)
  s-strength : ∀ {G T U} → Flat G → Supported (strength {T = T} {U = U} G)
  s-roll : ∀ {G} → (p : Flat G) → Supported (roll {G = G})
  s-P : ∀ {T U} (G : Ty FO 1)
        {h : (G [ T `× ind G ]) `× U →ᴾ T} →
        (p : Flat G) → Supported h →
        Supported (P {G = G} {T = T} {U = U} h)

eval : ∀ {T U} {f : T →ᴾ U} → Supported f → Sem T → Sem U
eval s-id x = x
eval (s-C sf sg) x = eval sf (eval sg x)
eval s-⊤ x = tt
eval s-⊥ ()
eval (s-# sf sg) x = eval sf x , eval sg x
eval s-π₁ (x , y) = x
eval s-π₂ (x , y) = y
eval s-ι₁ x = inj₁ x
eval s-ι₂ x = inj₂ x
eval (s-case sf sg) (inj₁ x) = eval sf x
eval (s-case sf sg) (inj₂ y) = eval sg y
eval s-dist (inj₁ x , z) = inj₁ (x , z)
eval s-dist (inj₂ y , z) = inj₂ (y , z)
eval (s-fmap p sf) x = fmapFlat p (eval sf) x
eval (s-strength p) x = strengthFlat p x
eval (s-roll p) x = rollFlat p x
eval (s-P {T = T} {U = U} G p sh) x =
  paraFlat {G = G} {T = T} {U = U} p (eval sh) x
