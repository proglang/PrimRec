module HVec where

open import Data.Fin using (Fin; suc; zero)
open import Data.List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_; _++_ to _++ᴸ_; length to lengthᴸ; map to mapᴸ)
open import Data.Vec using (Vec ;replicate) renaming ([] to []ⱽ; _∷_ to _∷ⱽ_ ) --  _++_; lookup; map; toList; head)
open import Data.Nat using (ℕ; suc; zero; _*_; _+_)


open import Utils



data HVec (F : S → Set) : ∀ {n : ℕ}  → Vec  S n → Set where
  []ᴴ  : HVec F []ⱽ
  _∷ᴴ_ : ∀ {n : ℕ} {s : S}  {ss : Vec S n} → F s → HVec F ss → HVec F (s ∷ⱽ ss)


data HIndex : ∀ {n : ℕ}  → Vec  S n → S → Set where
  ZI : ∀ {n : ℕ} {ss : Vec S n} {s} → HIndex (s ∷ⱽ ss) s
  SI : ∀ {n : ℕ} {ss : Vec S n} {s s'} → HIndex (ss) s → HIndex (s' ∷ⱽ ss) s



lkupH : ∀ {n : ℕ} {xs : Vec S n} {F : S → Set} {x} →   HIndex xs x → HVec F xs → F x
lkupH ZI (x ∷ᴴ xs) = x
lkupH (SI i) (x ∷ᴴ xs) = lkupH i xs


id : A → A 
id x = x

-- fromVec : ∀ {n : ℕ} {S : Set} → Vec S n →  HVec id (replicate S) 
-- fromVec xs = ?

toHVec : {S : Set} (v : Vec S n) → HVec (λ x → S) v
toHVec []ⱽ = []ᴴ
toHVec (x ∷ⱽ v) = x ∷ᴴ toHVec v




-- toHVec' : {n : ℕ} {S : Set} (v : Vec S n) → HVec  (λ x → {!   !}) (repeat {! n  !} {!S   !})
-- toHVec' []ⱽ = []ᴴ
-- toHVec' (x ∷ⱽ v) = x ∷ᴴ toHVec v



-- fromVec : ∀ {n : ℕ} {S : Set} → Vec ℕ n →  HVec id (replicate ℕ) 
-- fromVec xs = ?

-- hlookup : ∀ {ss : Vec S n}{F : S → Set} (a* : HList F (toList ss)) → (i : Fin n) → F (lookup ss i)
-- hlookup {ss = s ∷ ss} (a ∷ᴴ a*) Fin.zero = a
-- hlookup {ss = s ∷ ss} (a ∷ᴴ a*) (Fin.suc i) = hlookup a* i

-- _++ᴴ_ : ∀ {F : S → Set}{ss₁ ss₂ : List S} → HList F ss₁ → HList F ss₂ → HList F (ss₁ ++ᴸ ss₂)
-- []ᴴ ++ᴴ ys = ys
-- (x ∷ᴴ xs) ++ᴴ ys = x ∷ᴴ (xs ++ᴴ ys)

-- mapᴴ : ∀ {F : S → Set}{ss : List S} {res : S → S} → (∀ {s} → F s → F (res s)) → HList F ss → HList F (mapᴸ res ss)
-- mapᴴ f []ᴴ = []ᴴ
-- mapᴴ f (x ∷ᴴ a*) = f x ∷ᴴ mapᴴ f a*