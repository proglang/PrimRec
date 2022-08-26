module HTreesVec where

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; inspect; [_])
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; suc; zero; _*_; _+_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head; concat)
open import Data.Vec.Properties using (lookup-map)
open import Data.List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_; _++_ to _++ᴸ_; length to lengthᴸ; map to mapᴸ)
open import Function using (_∘_)

-- vector-valued primitive recursion for many-sorted algebras

variable
  A : Set                       -- alphabet
  S : Set                       -- set of sorts
  m n o : ℕ

Rank : Set → Set
Rank A = A → ℕ

HRank : Set → (A : Set) → (Rank A) → Set
HRank S A r = (a : A) → Vec S (r a) × Vec S 1

data PR {r} (hr : HRank S A r) : {m n : ℕ} → Vec S m × Vec S n → Set where
  `0 : ∀ {ssin : Vec S m} → PR hr ⟨ ssin , [] ⟩
  ♯  : ∀ {ssm : Vec S m} {ssn : Vec S n} {sso : Vec S o}
    → (g : PR hr ⟨ ssm , ssn ⟩) (f : PR hr ⟨ ssm , sso ⟩)
    → PR hr ⟨ ssm , ssn ++ sso ⟩

  σ  : (a : A)
    → PR hr (hr a)
  π  : ∀ {ssin : Vec S m}
    → (i : Fin m)
    → PR hr ⟨ ssin , lookup ssin i ∷ [] ⟩

  C  : ∀ {ssm : Vec S m} {ssn : Vec S n} {sso : Vec S o}
    → (f : PR hr ⟨ sso , ssn ⟩)
    → (g : PR hr ⟨ ssm , sso ⟩)
    → PR hr ⟨ ssm , ssn ⟩

  P  : ∀ {s₀}{ssm : Vec S m}
    → (res : S → Vec S n)
    → (h : (a : A) → head (proj₂ (hr a)) ≡ s₀
                   → PR hr ⟨ (concat (map res (proj₁ (hr a))) ++ proj₁ (hr a)) ++ ssm , res s₀ ⟩)
    → PR hr ⟨ s₀ ∷ ssm , res s₀ ⟩

data Alg  {A}{S}{r : Rank A} (hr : HRank S A r) : S → Set
data Alg* {A}{S}{r : Rank A} (hr : HRank S A r) : ∀ {n} → Vec S n → Set

data Alg {A}{S}{r} hr where
  con : (a : A) → Alg* hr (proj₁ (hr a)) → Alg hr (head (proj₂ (hr a))) 
data Alg* {A}{S}{r} hr where
  []*  : Alg* hr []
  _∷*_ : ∀ {s : S}{s* : Vec S n} → Alg hr s → Alg* hr s* → Alg* hr (s ∷ s*)

alookup : ∀ {r : Rank A}{hr : HRank S A r} {n} {s* : Vec S n}
  → Alg* hr {n} s* → (i : Fin n) → Alg hr (lookup s* i)
alookup (x ∷* _) zero = x
alookup (_ ∷* v*) (suc i) = alookup v* i

_++ᴬ_ : ∀ {r} {hr : HRank S A r} {ss₁ : Vec S m} {ss₂ : Vec S n}
  → Alg* hr ss₁ → Alg* hr ss₂ → Alg* hr (ss₁ ++ ss₂)
[]* ++ᴬ w* = w*
(x ∷* v*) ++ᴬ w* = x ∷* (v* ++ᴬ w*)

mapᴬ : ∀ {n}{r} {hr : HRank S A r} {ss : Vec S n} {res : S → S}
  → ((i : Fin n) → Alg hr (lookup ss i) → Alg hr (lookup (map res ss) i))
  → Alg* hr ss
  → Alg* hr (map res ss)
mapᴬ f []* = []*
mapᴬ f (x ∷* v*) = (f Fin.zero x) ∷* (mapᴬ (f ∘ Fin.suc) v*)

eval : ∀ {r : Rank A}{hr : HRank S A r}{ssm : Vec S m}{ssn : Vec S n}
  → PR hr ⟨ ssm , ssn ⟩
  → Alg* hr ssm
  → Alg* hr ssn

eval `0 v* = []*
eval (♯ f g) v* = eval f v* ++ᴬ eval g v*
eval {hr = hr} (σ a) v* = subst (Alg* hr) eq v
  where
    eq : head (proj₂ (hr a)) ∷ [] ≡ proj₂ (hr a)
    eq with hr a
    ... | ⟨ ssin , sout ∷ [] ⟩ = refl
    v : Alg* hr (head (proj₂ (hr a)) ∷ [])
    v = con a v* ∷* []*
eval (π i) v* = alookup v* i ∷* []*
eval (C f g) v* = eval f (eval g v*)
eval (P res h) (con a x* ∷* v*) = eval (h a refl) (({!!} ++ᴬ x*) ++ᴬ v*)
