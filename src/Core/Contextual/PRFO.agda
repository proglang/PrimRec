{-# OPTIONS --safe #-}

module Core.Contextual.PRFO where

open import Core.Types public

infix 6 _⊢_

variable
  Γ A B C D : TY FO
  G : Ty FO 1

data _⊢_ : TY FO → TY FO → Set where
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
  dist-+-× : (A `+ B) `× C ⊢ (A `× C) `+ (B `× C)

  fmap : (G : Ty FO 1) → (A ⊢ B) → (G [ A ] ⊢ G [ B ])
  strength : (G : Ty FO 1) → (G [ A ]) `× B ⊢ G [ A `× B ]

  con : G [ ind G ] ⊢ ind G
  prec : ((G [ A `× ind G ]) `× B ⊢ A)
    → (ind G `× B ⊢ A)

map-× : (A ⊢ C) → (B ⊢ D) → (A `× B ⊢ C `× D)
map-× f g = pair (cut f fst) (cut g snd)

pmap : (G : Ty FO 1) → (A `× B ⊢ C)
  → ((G [ A ]) `× B ⊢ G [ C ])
pmap G f = cut (fmap G f) (strength G)

paraArgs : (G : Ty FO 1) → (ind G `× B ⊢ A)
  → ((G [ ind G ]) `× B ⊢ (G [ A `× ind G ]) `× B)
paraArgs G p = pair (pmap G (pair p fst)) snd

undist-+-× : (A `× C) `+ (B `× C) ⊢ (A `+ B) `× C
undist-+-× = cases (pair (cut inl fst) snd) (pair (cut inr fst) snd)
