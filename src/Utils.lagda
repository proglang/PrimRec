\begin{code}
module Utils where

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; refl; cong)
open import Data.Nat using (ℕ; suc; zero; _*_; _+_)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head)
open import Function using (_∘_)


pattern [_] x = x ∷ []
pattern [_,_] x y = x ∷ y ∷ []

variable
  A : Set                       -- alphabet
  S : Set                       -- sorts for many-sorted
  m n o : ℕ

repeat : ∀ {ℓ} {A : Set ℓ} → (n : ℕ) → A → Vec A n
repeat zero a = []
repeat (suc n) a = a ∷ repeat n a

++-repeat : ∀ {m} {n} {ℓ} {A : Set ℓ} (x : A) → repeat (m + n) x ≡ repeat m x ++ repeat n x
++-repeat {zero} x = refl
++-repeat {suc m} x = cong (x ∷_) (++-repeat {m} x)

map-repeat : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → ∀ n (x : A) (f : A → B) → repeat n (f x) ≡ map f (repeat n x)
map-repeat zero x f = refl
map-repeat (suc n) x f rewrite map-repeat n x f = refl

++-map : ∀ {ℓ₁ ℓ₂} {m n}{X : Set ℓ₁}{Y : Set ℓ₂} → (f : X → Y)(v* : Vec X m)(w* : Vec X n) → (map f v* ++ map f w*) ≡ map f (v* ++ w*)
++-map f [] w* = refl
++-map f (v ∷ v*) w* = cong (f v ∷_) (++-map f v* w*)

∘-map : ∀ {ℓ₁ ℓ₂ ℓ₃} {n} {X : Set ℓ₁}{Y : Set ℓ₂}{Z : Set ℓ₃} (f : Y → Z) (g : X → Y) (v* : Vec X n) → map f (map g v*) ≡ map (f ∘ g) v*
∘-map f g [] = refl
∘-map f g (v ∷ v*) = cong ((f ∘ g) v ∷_) (∘-map f g v*)

asType : ∀ {A B : Set} → A → A ≡ B → B
asType a refl = a
\end{code}
