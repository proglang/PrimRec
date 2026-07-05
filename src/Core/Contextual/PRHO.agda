{-# OPTIONS --safe #-}

module Core.Contextual.PRHO where

open import Core.Types public

infix 6 _⊢_

variable
  Γ C : TY HO

----------------------------------------------------------------------
-- Contextual PR-HO with explicit substitution
--
-- A context is represented by its product object. Thus Γ ⊢ A is a
-- term of type A with one environment variable of type Γ. Finite
-- variable contexts elaborate to this presentation by nested products.
----------------------------------------------------------------------

data _⊢_ : TY HO → TY HO → Set where
  var : Γ ⊢ Γ
  cut : (B ⊢ C) → (Γ ⊢ B) → (Γ ⊢ C)

  unit  : Γ ⊢ `𝟙
  abort : `𝟘 ⊢ A

  pair : (Γ ⊢ A) → (Γ ⊢ B) → (Γ ⊢ A `× B)
  fst  : A `× B ⊢ A
  snd  : A `× B ⊢ B

  inl : A ⊢ A `+ B
  inr : B ⊢ A `+ B
  cases : (A ⊢ C) → (B ⊢ C) → (A `+ B ⊢ C)

  curry : (A `× B ⊢ C) → (A ⊢ B `⇒ C)
  eval  : (A `⇒ B) `× A ⊢ B

  fmap : (G : Ty HO 1) → (A ⊢ B) → (G [ A ] ⊢ G [ B ])
  strength : (G : Ty HO 1) → (G [ A ]) `× B ⊢ G [ A `× B ]

  con : G [ ind G ] ⊢ ind G
  prec : ((G [ A `× ind G ]) `× B ⊢ A)
    → (ind G `× B ⊢ A)

map-× : (A ⊢ C) → (B ⊢ D) → (A `× B ⊢ C `× D)
map-× f g = pair (cut f fst) (cut g snd)

fmapᶜ : ∀ {A B G} → StructuralFunctor G → (A ⊢ B) → (G [ A ] ⊢ G [ B ])
fmapᶜ sf-𝟘 f = var
fmapᶜ sf-𝟙 f = var
fmapᶜ sf-var f = f
fmapᶜ (sf-× p q) f = map-× (fmapᶜ p f) (fmapᶜ q f)
fmapᶜ (sf-+ p q) f =
  cases (cut inl (fmapᶜ p f)) (cut inr (fmapᶜ q f))
fmapᶜ (sf-⇒ A p) f = curry (cut (fmapᶜ p f) eval)

pmap : (G : Ty HO 1) → (A `× B ⊢ C)
  → ((G [ A ]) `× B ⊢ G [ C ])
pmap G f = cut (fmap G f) (strength G)

paraArgs : (G : Ty HO 1) → (ind G `× B ⊢ A)
  → ((G [ ind G ]) `× B ⊢ (G [ A `× ind G ]) `× B)
paraArgs G p = pair (pmap G (pair p fst)) snd

uncurry : (A ⊢ B `⇒ C) → (A `× B ⊢ C)
uncurry f = cut eval (map-× f var)

dist-+-× : (A `+ B) `× C ⊢ (A `× C) `+ (B `× C)
dist-+-× = uncurry (cases (curry inl) (curry inr))

undist-+-× : (A `× C) `+ (B `× C) ⊢ (A `+ B) `× C
undist-+-× = cases (pair (cut inl fst) snd) (pair (cut inr fst) snd)

strengthᶜ : ∀ {A B G} → StructuralFunctor G →
  (G [ A ]) `× B ⊢ G [ A `× B ]
strengthᶜ sf-𝟘 = fst
strengthᶜ sf-𝟙 = fst
strengthᶜ sf-var = var
strengthᶜ (sf-× p q) =
  pair
    (cut (strengthᶜ p) (pair (cut fst fst) snd))
    (cut (strengthᶜ q) (pair (cut snd fst) snd))
strengthᶜ (sf-+ p q) =
  cut (cases (cut inl (strengthᶜ p)) (cut inr (strengthᶜ q))) dist-+-×
strengthᶜ (sf-⇒ A p) =
  curry
    (cut (strengthᶜ p)
      (pair
        (cut eval (pair (cut fst fst) snd))
        (cut snd fst)))
