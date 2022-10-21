{-# OPTIONS --rewriting  #-}
module HVec where

open import Data.Fin using (Fin; suc; zero)
open import Data.List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_; _++_ to _++ᴸ_; length to lengthᴸ; map to mapᴸ)
open import Data.Vec using (Vec ;replicate; lookup; _++_; map) -- ; [],_∷_) -- renaming ([] to []ⱽ; _∷_ to _∷ⱽ_ ) --  _++_; lookup; map; toList; head)
open import Data.Nat using (ℕ; suc; zero; _*_; _+_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂)

open import VecProperties
open Vec

open import Utils


data HVec (F : S → Set) : ∀ {n} → Vec S n → Set where
  []ᴴ  : HVec F []
  _∷ᴴ_ : ∀ {n s ss} → F s → HVec F {n} ss → HVec F (s ∷ ss)

hlookup : ∀ {ss : Vec S n}{F : S → Set} (a* : HVec F ss) → (i : Fin n) → F (lookup ss i)
hlookup {ss = s ∷ ss} (a ∷ᴴ a*) Fin.zero = a
hlookup {ss = s ∷ ss} (a ∷ᴴ a*) (Fin.suc i) = hlookup a* i

infixr 5 _++ᴴ_

_++ᴴ_ : ∀ {F : S → Set}{n₁ n₂}{ss₁ : Vec S n₁}{ss₂ : Vec S n₂} → HVec F ss₁ → HVec F ss₂ → HVec F (ss₁ ++ ss₂)
[]ᴴ ++ᴴ ys = ys
(x ∷ᴴ xs) ++ᴴ ys = x ∷ᴴ (xs ++ᴴ ys)

mapᴴ' : ∀ {S T : Set} {F : S → Set}{G : T → Set}{n}{ss : Vec S n} {res : S → T} → (∀ {s} → F s → G (res s)) → HVec F ss → HVec G (map res ss)
mapᴴ' f []ᴴ = []ᴴ
mapᴴ'  {ss = s' ∷ ss'}{res = res'} f (x ∷ᴴ a*) = f x ∷ᴴ mapᴴ'  f a* -- 

mapᴴ : ∀ {F : S → Set}{n}{ss : Vec S n} {res : S → S} → (∀ {s} → F s → F (res s)) → HVec F ss → HVec F (map res ss)
mapᴴ f []ᴴ = []ᴴ
mapᴴ f (x ∷ᴴ a*) = f x ∷ᴴ mapᴴ f a*


toHVec : {S : Set} (v : Vec S n) → HVec (λ x → S) v
toHVec [] = []ᴴ
toHVec (x ∷ v) = x ∷ᴴ toHVec v

data HIndex : ∀ {n : ℕ}  → Vec  S n → S → Set where
  ZI : ∀ {n : ℕ} {ss : Vec S n} {s} → HIndex (s ∷ ss) s
  SI : ∀ {n : ℕ} {ss : Vec S n} {s s'} → HIndex (ss) s → HIndex (s' ∷ ss) s


lkupH : ∀ {n : ℕ} {xs : Vec S n} {F : S → Set} {x} →   HIndex xs x → HVec F xs → F x
lkupH ZI (x ∷ᴴ xs) = x
lkupH (SI i) (x ∷ᴴ xs) = lkupH i xs

_++rᴴ_ : ∀ {F : S → Set}{m n : ℕ}   {xs : Vec S m}{ys : Vec S n}→ HVec F xs → HVec F ys → HVec F (xs ++r ys)
(x ∷ᴴ xs)      ++rᴴ ys = xs ++rᴴ (x ∷ᴴ ys)
[]ᴴ ++rᴴ ys = ys


fastReverseᴴ : ∀ {F : S → Set}{ n : ℕ}   {xs : Vec S n} → HVec F xs → HVec F (fastReverse xs) 
fastReverseᴴ xs = xs ++rᴴ []ᴴ

{-# REWRITE ++identityR #-}


++identityRᴴ : ∀ {F : S → Set}{ n : ℕ}   {xs : Vec S n} → ( xs' :  HVec F xs)→ xs' ++ᴴ []ᴴ ≡ xs'
++identityRᴴ []ᴴ = refl
++identityRᴴ (x ∷ᴴ xs) = cong (λ v → x ∷ᴴ v) (++identityRᴴ xs)

-- id : A → A 
-- id x = x


-- toHVec : {S : Set} (v : Vec S n) → HVec (λ x → S) v
-- toHVec []ⱽ = []ᴴ
-- toHVec (x ∷ⱽ v) = x ∷ᴴ toHVec v

-- mapᴴ : ∀{n}{F : S → Set}{ss rss : Vec S n} → (∀ {i : Fin n} → F (lookup ss i) → F (lookup rss i)) → HVec F ss → HVec F rss
-- mapᴴ{rss = []ⱽ} f []ᴴ = []ᴴ
-- mapᴴ{rss = A ∷ⱽ V} f (a ∷ᴴ a*) = f {zero} a ∷ᴴ mapᴴ (λ{i} → f{suc i}) a*


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

