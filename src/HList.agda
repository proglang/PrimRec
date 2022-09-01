module HList where

open import Data.Fin using (Fin; suc; zero)
open import Data.List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_; _++_ to _++ᴸ_; length to lengthᴸ; map to mapᴸ)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head)

open import Utils

data HList (F : S → Set) : List S → Set where
  []ᴴ  : HList F []ᴸ
  _∷ᴴ_ : ∀ {s ss} → F s → HList F ss → HList F (s ∷ᴸ ss)


hlookup : ∀ {ss : Vec S n}{F : S → Set} (a* : HList F (toList ss)) → (i : Fin n) → F (lookup ss i)
hlookup {ss = s ∷ ss} (a ∷ᴴ a*) Fin.zero = a
hlookup {ss = s ∷ ss} (a ∷ᴴ a*) (Fin.suc i) = hlookup a* i

_++ᴴ_ : ∀ {F : S → Set}{ss₁ ss₂ : List S} → HList F ss₁ → HList F ss₂ → HList F (ss₁ ++ᴸ ss₂)
[]ᴴ ++ᴴ ys = ys
(x ∷ᴴ xs) ++ᴴ ys = x ∷ᴴ (xs ++ᴴ ys)

mapᴴ : ∀ {F : S → Set}{ss : List S} {res : S → S} → (∀ {s} → F s → F (res s)) → HList F ss → HList F (mapᴸ res ss)
mapᴴ f []ᴴ = []ᴴ
mapᴴ f (x ∷ᴴ a*) = f x ∷ᴴ mapᴴ f a*

