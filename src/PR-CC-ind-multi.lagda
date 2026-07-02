\begin{code}
module PR-CC-ind-multi where

open import Data.Fin using (Fin; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List using (List; [] ; _∷_; _++_; concat)
import Data.List as List
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Vec using (Vec;[];_∷_;map;lookup;foldr)
open import Data.Product using (_×_; proj₁; proj₂; <_,_>) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; const)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂)
open Eq.≡-Reasoning using (begin_; step-≡-⟩; _∎)
open import Utils

infix 6 _→ᴾ_
infix 7 `××_
infix 8 `++_

data Ty n : Set where
  `××_ : Vec (Ty n) m → Ty n
  `++_ : Vec (Ty n) m → Ty n
  `    : Fin n → Ty n
  ind  : Ty (suc n) → Ty n

Ren : ℕ → ℕ → Set
Ren n m = Fin n → Fin m

extᴿ : Ren n m → Ren (suc n) (suc m)
extᴿ ρ zero    = zero
extᴿ ρ (suc x) = suc (ρ x)

ren : Ren n m → Ty n → Ty m
ren* : Ren n m → Vec (Ty n) o → Vec (Ty m) o

ren ρ (`×× U*) = `×× ren* ρ U*
ren ρ (`++ U*) = `++ ren* ρ U*
ren ρ (` x)    = ` (ρ x)
ren ρ (ind G)  = ind (ren (extᴿ ρ) G)

ren* ρ [] = []
ren* ρ (U ∷ U*) = ren ρ U ∷ ren* ρ U*

Sub : ℕ → ℕ → Set
Sub n m = Fin n → Ty m

extˢ : Sub n m → Sub (suc n) (suc m)
extˢ σ zero    = ` zero
extˢ σ (suc x) = ren suc (σ x)

sub : Sub n m → Ty n → Ty m
sub* : Sub n m → Vec (Ty n) o → Vec (Ty m) o

sub σ (`×× U*) = `×× sub* σ U*
sub σ (`++ U*) = `++ sub* σ U*
sub σ (` x)    = σ x
sub σ (ind G)  = ind (sub (extˢ σ) G)

sub* σ [] = []
sub* σ (U ∷ U*) = (sub σ U) ∷ (sub* σ U*)

idₛ : Sub n n
idₛ x = ` x

σ₀ : Ty n → Sub (suc n) n
σ₀ T zero = T
σ₀ T (suc x) = ` x

sub₀ : Ty 0 → Ty 1 → Ty 0
sub₀ T G = sub (σ₀ T) G

infix 4 _~_
_~_ : ∀ {A : Set} {B : A → Set} → ((x : A) → B x) → ((x : A) → B x) → Set
f ~ g = ∀ x → f x ≡ g x

extˢ-cong : ∀ {σ τ : Sub n m} → σ ~ τ → extˢ σ ~ extˢ τ
extˢ-cong h zero = refl
extˢ-cong h (suc x) = cong (ren suc) (h x)

ren-cong : ∀ {ρ τ : Ren n m} → ρ ~ τ → (T : Ty n) → ren ρ T ≡ ren τ T
ren*-cong : ∀ {ρ τ : Ren n m} → ρ ~ τ → (T* : Vec (Ty n) o) → ren* ρ T* ≡ ren* τ T*

ren-cong h (`×× T*) = cong `××_ (ren*-cong h T*)
ren-cong h (`++ T*) = cong `++_ (ren*-cong h T*)
ren-cong h (` x) = cong (λ i → ` i) (h x)
ren-cong h (ind G) = cong ind (ren-cong (extᴿ-cong h) G)
  where
  extᴿ-cong : ∀ {ρ τ : Ren n m} → ρ ~ τ → extᴿ ρ ~ extᴿ τ
  extᴿ-cong h zero = refl
  extᴿ-cong h (suc x) = cong suc (h x)
ren*-cong h [] = refl
ren*-cong h (T ∷ T*) = cong₂ _∷_ (ren-cong h T) (ren*-cong h T*)

sub-cong : ∀ {σ τ : Sub n m} → σ ~ τ → (T : Ty n) → sub σ T ≡ sub τ T
sub*-cong : ∀ {σ τ : Sub n m} → σ ~ τ → (T* : Vec (Ty n) o) → sub* σ T* ≡ sub* τ T*

sub-cong h (`×× T*) = cong `××_ (sub*-cong h T*)
sub-cong h (`++ T*) = cong `++_ (sub*-cong h T*)
sub-cong h (` x) = h x
sub-cong h (ind G) = cong ind (sub-cong (extˢ-cong h) G)
sub*-cong h [] = refl
sub*-cong h (T ∷ T*) = cong₂ _∷_ (sub-cong h T) (sub*-cong h T*)

ren-ren : (ρ : Ren n m) (τ : Ren m o) (T : Ty n)
  → ren τ (ren ρ T) ≡ ren (τ ∘ ρ) T
ren*-ren* : ∀ {p} → (ρ : Ren n m) (τ : Ren m o) (T* : Vec (Ty n) p)
  → ren* τ (ren* ρ T*) ≡ ren* (τ ∘ ρ) T*

ren-ren ρ τ (`×× T*) = cong `××_ (ren*-ren* ρ τ T*)
ren-ren ρ τ (`++ T*) = cong `++_ (ren*-ren* ρ τ T*)
ren-ren ρ τ (` x) = refl
ren-ren ρ τ (ind G) = cong ind
  (trans (ren-ren (extᴿ ρ) (extᴿ τ) G)
    (ren-cong (extᴿ-∘ ρ τ) G))
  where
  extᴿ-∘ : (ρ : Ren n m) (τ : Ren m o) → (extᴿ τ ∘ extᴿ ρ) ~ extᴿ (τ ∘ ρ)
  extᴿ-∘ ρ τ zero = refl
  extᴿ-∘ ρ τ (suc x) = refl
ren*-ren* ρ τ [] = refl
ren*-ren* ρ τ (T ∷ T*) = cong₂ _∷_ (ren-ren ρ τ T) (ren*-ren* ρ τ T*)

ren-sub : (ρ : Ren n m) (τ : Sub m o) (T : Ty n)
  → sub τ (ren ρ T) ≡ sub (τ ∘ ρ) T
ren*-sub* : ∀ {p} → (ρ : Ren n m) (τ : Sub m o) (T* : Vec (Ty n) p)
  → sub* τ (ren* ρ T*) ≡ sub* (τ ∘ ρ) T*

ren-sub ρ τ (`×× T*) = cong `××_ (ren*-sub* ρ τ T*)
ren-sub ρ τ (`++ T*) = cong `++_ (ren*-sub* ρ τ T*)
ren-sub ρ τ (` x) = refl
ren-sub ρ τ (ind G) = cong ind
  (trans (ren-sub (extᴿ ρ) (extˢ τ) G)
    (sub-cong (ext-rs ρ τ) G))
  where
  ext-rs : (ρ : Ren n m) (τ : Sub m o) → (extˢ τ ∘ extᴿ ρ) ~ extˢ (τ ∘ ρ)
  ext-rs ρ τ zero = refl
  ext-rs ρ τ (suc x) = refl
ren*-sub* ρ τ [] = refl
ren*-sub* ρ τ (T ∷ T*) = cong₂ _∷_ (ren-sub ρ τ T) (ren*-sub* ρ τ T*)

sub-ren : (σ : Sub n m) (ρ : Ren m o) (T : Ty n)
  → ren ρ (sub σ T) ≡ sub (ren ρ ∘ σ) T
sub*-ren* : ∀ {p} → (σ : Sub n m) (ρ : Ren m o) (T* : Vec (Ty n) p)
  → ren* ρ (sub* σ T*) ≡ sub* (ren ρ ∘ σ) T*

sub-ren σ ρ (`×× T*) = cong `××_ (sub*-ren* σ ρ T*)
sub-ren σ ρ (`++ T*) = cong `++_ (sub*-ren* σ ρ T*)
sub-ren σ ρ (` x) = refl
sub-ren σ ρ (ind G) = cong ind
  (trans (sub-ren (extˢ σ) (extᴿ ρ) G)
    (sub-cong (ext-sr σ ρ) G))
  where
  ext-sr : (σ : Sub n m) (ρ : Ren m o) → (ren (extᴿ ρ) ∘ extˢ σ) ~ extˢ (ren ρ ∘ σ)
  ext-sr σ ρ zero = refl
  ext-sr σ ρ (suc x) = trans (ren-ren suc (extᴿ ρ) (σ x)) (sym (ren-ren ρ suc (σ x)))
sub*-ren* σ ρ [] = refl
sub*-ren* σ ρ (T ∷ T*) = cong₂ _∷_ (sub-ren σ ρ T) (sub*-ren* σ ρ T*)

_ˢ⨟ˢ_ : Sub n m → Sub m o → Sub n o
(σ ˢ⨟ˢ τ) x = sub τ (σ x)

ext-ˢ⨟ˢ : (σ : Sub n m) (τ : Sub m o) → (extˢ σ ˢ⨟ˢ extˢ τ) ~ extˢ (σ ˢ⨟ˢ τ)
ext-ˢ⨟ˢ σ τ zero = refl
ext-ˢ⨟ˢ σ τ (suc x) =
  trans (ren-sub suc (extˢ τ) (σ x)) (sym (sub-ren τ suc (σ x)))

sub-sub : (σ : Sub n m) (τ : Sub m o) (T : Ty n)
  → sub τ (sub σ T) ≡ sub (σ ˢ⨟ˢ τ) T
sub*-sub* : ∀ {p} → (σ : Sub n m) (τ : Sub m o) (T* : Vec (Ty n) p)
  → sub* τ (sub* σ T*) ≡ sub* (σ ˢ⨟ˢ τ) T*

sub-sub σ τ (`×× T*) = cong `××_ (sub*-sub* σ τ T*)
sub-sub σ τ (`++ T*) = cong `++_ (sub*-sub* σ τ T*)
sub-sub σ τ (` x) = refl
sub-sub σ τ (ind G) = cong ind
  (trans (sub-sub (extˢ σ) (extˢ τ) G)
    (sub-cong (ext-ˢ⨟ˢ σ τ) G))
sub*-sub* σ τ [] = refl
sub*-sub* σ τ (T ∷ T*) = cong₂ _∷_ (sub-sub σ τ T) (sub*-sub* σ τ T*)

extˢ-idₛ : extˢ (idₛ {n}) ~ idₛ
extˢ-idₛ zero = refl
extˢ-idₛ (suc x) = refl

sub-idₛ : (T : Ty n) → sub idₛ T ≡ T
sub*-idₛ : (T* : Vec (Ty n) o) → sub* idₛ T* ≡ T*
sub-idₛ (`×× T*) = cong `××_ (sub*-idₛ T*)
sub-idₛ (`++ T*) = cong `++_ (sub*-idₛ T*)
sub-idₛ (` x) = refl
sub-idₛ (ind G) = cong ind (trans (sub-cong extˢ-idₛ G) (sub-idₛ G))
sub*-idₛ [] = refl
sub*-idₛ (T ∷ T*) = cong₂ _∷_ (sub-idₛ T) (sub*-idₛ T*)

wk-cancel : (R : Ty n) (T : Ty n) → sub (σ₀ R) (ren suc T) ≡ T
wk-cancel R T = begin
  sub (σ₀ R) (ren suc T)
    ≡⟨ ren-sub suc (σ₀ R) T ⟩
  sub ((σ₀ R) ∘ suc) T
    ≡⟨ sub-cong (λ x → refl) T ⟩
  sub idₛ T
    ≡⟨ sub-idₛ T ⟩
  T ∎

comm-unfold : (τ : Sub 1 0) (H : Ty 2)
  → (σ₀ (ind H) ˢ⨟ˢ τ) ~ (extˢ τ ˢ⨟ˢ σ₀ (ind (sub (extˢ τ) H)))
comm-unfold τ H zero = refl
comm-unfold τ H (suc zero) = sym (wk-cancel (ind (sub (extˢ τ) H)) (τ zero))

eq-unfold : (τ : Sub 1 0) (H : Ty 2)
  → sub τ (sub (σ₀ (ind H)) H)
    ≡ sub₀ (ind (sub (extˢ τ) H)) (sub (extˢ τ) H)
eq-unfold τ H = begin
  sub τ (sub (σ₀ (ind H)) H)
    ≡⟨ sub-sub (σ₀ (ind H)) τ H ⟩
  sub (σ₀ (ind H) ˢ⨟ˢ τ) H
    ≡⟨ sub-cong (comm-unfold τ H) H ⟩
  sub (extˢ τ ˢ⨟ˢ σ₀ (ind (sub (extˢ τ) H))) H
    ≡⟨ sym (sub-sub (extˢ τ) (σ₀ (ind (sub (extˢ τ) H))) H) ⟩
  sub₀ (ind (sub (extˢ τ) H)) (sub (extˢ τ) H) ∎

TY = Ty 0

variable
  T U V : TY
  U* : Vec TY o
  G : Ty 1

{-# NO_POSITIVITY_CHECK #-}
data _→ᴾ_ : TY → TY → Set where
  P : (h : `×× (sub₀ (`×× [ T , ind G ]) G ∷ U*) →ᴾ T)
    → (`×× (ind G ∷ U*) →ᴾ T)
  roll : sub₀ (ind G) G →ᴾ ind G
  --
  C : (f : U →ᴾ V)
    → (g : T →ᴾ U)
    → (T →ᴾ V)
  --
  π : {T* : Vec TY n} → (i : Fin n) → `×× T* →ᴾ lookup T* i
  `prod : foldr (const Set) (λ U t → T →ᴾ U × t) ⊤ U* → T →ᴾ `×× U*
  --
  ι : {T* : Vec TY n} → (i : Fin n) → lookup T* i →ᴾ `++ T*
  `case : foldr (const Set) (λ U t → U →ᴾ T × t) ⊤ U* → `++ U* →ᴾ T
  -- distributivity of a binary sum over the remaining product components
  dist-+-x : {T* : Vec TY n}
    → `×× (`++ [ U , V ] ∷ T*)
    →ᴾ `++ [ `×× (U ∷ T*) , `×× (V ∷ T*) ]

-- -- interpretation

⟦_⟧ᵀ : TY → Set
⟦_⟧ᵀ× : Vec TY o → Set
⟦_⟧ᵀ+ : Vec TY o → Set

data Alg (G : Ty 1) : Set where
  roll : ⟦ sub₀ (ind G) G ⟧ᵀ → Alg G 

⟦ `×× U* ⟧ᵀ = ⟦ U* ⟧ᵀ×
⟦ `++ U* ⟧ᵀ = ⟦ U* ⟧ᵀ+
⟦ ind G ⟧ᵀ = Alg G

⟦ [] ⟧ᵀ× = ⊤
⟦ U ∷ U* ⟧ᵀ× = ⟦ U ⟧ᵀ × ⟦ U* ⟧ᵀ×

⟦ [] ⟧ᵀ+ = ⊥
⟦ U ∷ U* ⟧ᵀ+ = ⟦ U ⟧ᵀ ⊎ ⟦ U* ⟧ᵀ+

{-# TERMINATING #-}
fmap : ∀ {S T : TY} (G : Ty 1)
  → (⟦ S ⟧ᵀ → ⟦ T ⟧ᵀ)
  → ⟦ sub₀ S G ⟧ᵀ → ⟦ sub₀ T G ⟧ᵀ
fmap× : ∀ {S T : TY} (G* : Vec (Ty 1) n)
  → (⟦ S ⟧ᵀ → ⟦ T ⟧ᵀ)
  → ⟦ sub* (σ₀ S) G* ⟧ᵀ× → ⟦ sub* (σ₀ T) G* ⟧ᵀ×
fmap+ : ∀ {S T : TY} (G* : Vec (Ty 1) n)
  → (⟦ S ⟧ᵀ → ⟦ T ⟧ᵀ)
  → ⟦ sub* (σ₀ S) G* ⟧ᵀ+ → ⟦ sub* (σ₀ T) G* ⟧ᵀ+

fmap (`×× G*) f x = fmap× G* f x
fmap (`++ G*) f x = fmap+ G* f x
fmap (` zero) f x = f x
fmap {S} {T} (ind H) f (roll x)
  rewrite sym (eq-unfold (σ₀ S) H)
  with fmap {S} {T} (sub (σ₀ (ind H)) H) f x
... | ih rewrite eq-unfold (σ₀ T) H = roll ih

fmap× [] f tt = tt
fmap× (G ∷ G*) f ⟨ x , x* ⟩ = ⟨ fmap G f x , fmap× G* f x* ⟩

fmap+ [] f ()
fmap+ (G ∷ G*) f (inj₁ x) = inj₁ (fmap G f x)
fmap+ (G ∷ G*) f (inj₂ x*) = inj₂ (fmap+ G* f x*)

-- fmap : ∀ {T} {G₀ : Ty 1}
--   → (f : ⟦ ind G₀ ⟧ᵀ → ⟦ T ⟧ᵀ) (G : Ty 1)
--   → ⟦ sub₀ (ind G₀) G ⟧ᵀ → ⟦ sub₀ T G ⟧ᵀ
-- fmap f `𝟙 tt = tt
-- fmap f (G `× H) (x , y) = (fmap f G x) , (fmap f H y)
-- fmap f (G `+ H) (inj₁ x) = inj₁ (fmap f G x)
-- fmap f (G `+ H) (inj₂ y) = inj₂ (fmap f H y)
-- fmap f (` zero) v = f v
-- fmap f (ind G) (roll x) = roll {!!}
-- --- needs to be recursive over `ind G`

-- fmap′ : ∀ {T} → {G₀ : Ty 1} (f : ⟦ ind G₀ ⟧ᵀ → ⟦ T ⟧ᵀ) (G : Ty 1) → ⟦ sub₀ (ind G₀) G ⟧ᵀ → ⟦ sub₀ (T `× ind G₀) G ⟧ᵀ
-- fmap′ f `𝟙 tt = tt
-- fmap′ f (G `× H) (x , y) = (fmap′ f G x) , (fmap′ f H y)
-- fmap′ f (G `+ H) (inj₁ x) = inj₁ (fmap′ f G x)
-- fmap′ f (G `+ H) (inj₂ y) = inj₂ (fmap′ f H y)
-- fmap′ f (` zero) v = f v , v
-- fmap′ {_}{G₀} f (ind G) (roll x) =
--   let G′ : Ty 1
--       G′ = sub (λ{ zero → ind G ; (suc zero) → ` zero}) G
--       r′ = fmap′ f G′ {!x!}
--   in roll {!!}
-- --- needs to be recursive over `ind G`

project : {T* : Vec TY n} → (i : Fin n) → ⟦ T* ⟧ᵀ× → ⟦ lookup T* i ⟧ᵀ
project {T* = T ∷ T*} zero ⟨ t , _ ⟩ = t
project {T* = T ∷ T*} (suc i) ⟨ _ , t* ⟩ = project i t*

inject : {T* : Vec TY n} → (i : Fin n) → ⟦ lookup T* i ⟧ᵀ → ⟦ T* ⟧ᵀ+
inject {T* = T ∷ T*} zero t = inj₁ t
inject {T* = T ∷ T*} (suc i) t = inj₂ (inject i t)

{-# TERMINATING #-}
eval-P-hard : ∀ {T}{G : Ty 1}{U* : Vec TY o}
  → (p : `×× (sub₀ (`×× [ T , ind G ]) G ∷ U*) →ᴾ T)
  → ⟦ `×× (ind G ∷ U*) ⟧ᵀ → ⟦ T ⟧ᵀ
product : ∀ {U* : Vec TY m} → foldr (const Set) (λ U → _×_ (T →ᴾ U)) ⊤ U* → ⟦ T ⟧ᵀ → ⟦ U* ⟧ᵀ×
sum     : ∀ {U* : Vec TY m} → foldr (const Set) (λ U → _×_ (U →ᴾ T)) ⊤ U* → ⟦ U* ⟧ᵀ+ → ⟦ T ⟧ᵀ

eval : (T →ᴾ U) → ⟦ T ⟧ᵀ → ⟦ U ⟧ᵀ
eval-P-hard {T = T} {G = G} {U* = U*} p ⟨ roll x , u* ⟩ =
  eval p
    ⟨ fmap G
        (λ v → ⟨ eval-P-hard p ⟨ v , u* ⟩ , ⟨ v , tt ⟩ ⟩)
        x
    , u* ⟩

eval (P p) = eval-P-hard p

eval roll = roll
eval (C f g) = eval f ∘ eval g
eval (π i) = project i
eval (`prod g*) = product g*
eval (ι i) = inject i
eval (`case g*) = sum g*
eval dist-+-x = λ
  { ⟨ inj₁ x , t* ⟩ → inj₁ ⟨ x , t* ⟩
  ; ⟨ inj₂ (inj₁ y) , t* ⟩ → inj₂ (inj₁ ⟨ y , t* ⟩)
  ; ⟨ inj₂ (inj₂ ()) , t* ⟩
  }

product {U* = []} g* t = tt
product {U* = U ∷ U*} ⟨ g , g* ⟩ t = ⟨ eval g t , product g* t ⟩

sum {U* = U ∷ U*} ⟨ g , g* ⟩ (inj₁ x) = eval g x
sum {U* = U ∷ U*} ⟨ g , g* ⟩ (inj₂ y) = sum g* y


-- {-# TERMINATING #-}
-- eval : (T →ᴾ U) → ⟦ T ⟧ᵀ → ⟦ U ⟧ᵀ
-- eval (F {G = G} p) = λ{ (roll x , u) → eval p ((fmap (λ v → eval (F p) (v , u)) G x) , (x , u))}
-- eval (P {G = G} p) = λ{ (roll x , u) → eval p ((fmap′ (λ v → eval (P p) (v , u)) G x) , u)}
-- eval (C f g)  = eval f ∘ eval g
-- eval roll     = roll
-- eval `0       = const tt
-- eval id       = λ v → v
-- eval (`# f g) = < eval f , eval g >
-- eval π₁       = proj₁
-- eval π₂       = proj₂
-- eval ι₁       = inj₁
-- eval ι₂       = inj₂
-- eval (`case f g) = λ{ (inj₁ x) → eval f x ; (inj₂ y) → eval g y}
-- \end{code}


mkvec : Ty 0 → ℕ → Ty 0
mkvec T n = `×× repeat n T

-- Package an indexed family of maps as the argument expected by `prod.
arrows : ∀ {S : TY} {T* : Vec TY n}
  → ((i : Fin n) → S →ᴾ lookup T* i)
  → foldr (const Set) (λ U t → S →ᴾ U × t) ⊤ T*
arrows {T* = []} f = tt
arrows {T* = T ∷ T*} f =
  ⟨ f zero , arrows {T* = T*} (λ i → f (suc i)) ⟩

tail : {T : TY} {T* : Vec TY n} → `×× (T ∷ T*) →ᴾ `×× T*
tail {T* = T*} = `prod (arrows {T* = T*} (λ i → π (suc i)))

lookupᴾ : (i : Fin n) → mkvec T n →ᴾ T
lookupᴾ zero = π zero
lookupᴾ (suc i) = C (lookupᴾ i) tail

assoc-× : {T* : Vec TY n}
  → `×× (`×× [ U , V ] ∷ T*) →ᴾ `×× (U ∷ V ∷ T*)
assoc-× {T* = T*} = `prod
  ⟨ C (π zero) (π zero)
  , ⟨ C (π (suc zero)) (π zero)
    , arrows {T* = T*} (λ i → π (suc i)) ⟩ ⟩

drop-counter : {T* : Vec TY n}
  → `×× (`×× [ U , V ] ∷ T*) →ᴾ `×× (U ∷ T*)
drop-counter {T* = T*} = `prod
  ⟨ C (π zero) (π zero)
  , arrows {T* = T*} (λ i → π (suc i)) ⟩

cons-prod : {S : TY} → (S →ᴾ T) → (S →ᴾ `×× U*) → S →ᴾ `×× (T ∷ U*)
cons-prod {U* = U*} f g =
  `prod ⟨ f , arrows {T* = U*} (λ i → C (π i) g) ⟩

module FromNats where
  G-Nat : Ty 1
  G-Nat = `++ [ `×× [] , ` zero ]

  Nat = ind G-Nat

  import PR-Nat as Nats

  ⟦_⟧  : Nats.PR n → mkvec Nat n →ᴾ Nat
  ⟦_⟧* : Vec (Nats.PR n) m → mkvec Nat n →ᴾ mkvec Nat m

  ⟦ Nats.Z ⟧      = C roll (ι zero)
  ⟦ Nats.σ ⟧      = C roll (C (ι (suc zero)) (π zero))
  ⟦ Nats.π i ⟧    = lookupᴾ i
  ⟦ Nats.C f g* ⟧ = C ⟦ f ⟧ ⟦ g* ⟧*
  ⟦ Nats.P g h ⟧  = P (C
    (`case ⟨ C ⟦ g ⟧ tail , ⟨ C ⟦ h ⟧ assoc-× , tt ⟩ ⟩)
    dist-+-x)
  ⟦ Nats.F g h ⟧  = P (C
    (`case ⟨ C ⟦ g ⟧ tail , ⟨ C ⟦ h ⟧ drop-counter , tt ⟩ ⟩)
    dist-+-x)

  ⟦ [] ⟧*         = `prod tt
  ⟦ p ∷ p* ⟧*     = cons-prod ⟦ p ⟧ ⟦ p* ⟧*

module FromWords where
  Alpha : Ty 0
  Alpha = `++ [ `×× [] , `×× [] ]

  G-Alpha* : Ty 1
  G-Alpha* = `++ [ `×× [] , `×× [ ren suc Alpha , ` zero ] ]

  Alpha* : Ty 0
  Alpha* = ind G-Alpha*

  ⟦_⟧ᴬ : ⟦ Alpha ⟧ᵀ → `×× [] →ᴾ Alpha
  ⟦ inj₁ tt ⟧ᴬ = ι zero
  ⟦ inj₂ (inj₁ tt) ⟧ᴬ = ι (suc zero)
  ⟦ inj₂ (inj₂ ()) ⟧ᴬ

  import PR-Words as Words

  ⟦_⟧  : Words.PR ⟦ Alpha ⟧ᵀ n → mkvec Alpha* n →ᴾ Alpha*
  ⟦_⟧* : Vec (Words.PR ⟦ Alpha ⟧ᵀ n) m
    → mkvec Alpha* n →ᴾ mkvec Alpha* m

  ⟦ Words.Z ⟧ = C roll (ι zero)
  ⟦ Words.σ a ⟧ = C roll (C (ι (suc zero)) (`prod
    ⟨ C ⟦ a ⟧ᴬ tail , ⟨ π zero , tt ⟩ ⟩))
  ⟦ Words.π i ⟧ = lookupᴾ i
  ⟦ Words.C f g* ⟧ = C ⟦ f ⟧ ⟦ g* ⟧*
  ⟦ Words.P g h ⟧ = P (C
    (`case
      ⟨ C ⟦ g ⟧ tail
      , ⟨ C
          (`case
            ⟨ C ⟦ h (inj₁ tt) ⟧ (C assoc-× tail)
            , ⟨ C ⟦ h (inj₂ (inj₁ tt)) ⟧ (C assoc-× tail)
              , tt ⟩ ⟩)
          (C dist-+-x assoc-×)
        , tt ⟩ ⟩)
    dist-+-x)

  ⟦ [] ⟧*         = `prod tt
  ⟦ p ∷ p* ⟧*     = cons-prod ⟦ p ⟧ ⟦ p* ⟧*

module FromTrees where
  infixr 5 _∷ᴾ_

  variable
    H : Ty 1
    G* : Vec (Ty 1) n

  unit : Ty 0
  unit = `×× []

  symbols : Ty 1 → Set
  symbols G = ⟦ sub₀ unit G ⟧ᵀ

  symbols× : Vec (Ty 1) n → Set
  symbols× G* = ⟦ sub* (σ₀ unit) G* ⟧ᵀ×

  symbols+ : Vec (Ty 1) n → Set
  symbols+ G* = ⟦ sub* (σ₀ unit) G* ⟧ᵀ+

  mutual
    data Poly : Ty 1 → Set where
      poly-prod : Poly* G* → Poly (`×× G*)
      poly-sum  : Poly* G* → Poly (`++ G*)
      poly-var  : Poly (` zero)

    data Poly* : Vec (Ty 1) n → Set where
      []ᴾ  : Poly* []
      _∷ᴾ_ : Poly G → Poly* G* → Poly* (G ∷ G*)

  poly-unit : Poly (`×× [])
  poly-unit = poly-prod []ᴾ

  poly-pair : Poly G → Poly H → Poly (`×× [ G , H ])
  poly-pair pg ph = poly-prod (pg ∷ᴾ ph ∷ᴾ []ᴾ)

  mutual
    dom : Poly G → List (symbols G)
    dom× : (p* : Poly* G*) → List (symbols× G*)
    dom+ : (p* : Poly* G*) → List (symbols+ G*)

    dom (poly-prod p*) = dom× p*
    dom (poly-sum p*) = dom+ p*
    dom poly-var = tt ∷ []

    dom× []ᴾ = tt ∷ []
    dom× (p ∷ᴾ p*) = concat
      (List.map (λ x → List.map (λ x* → ⟨ x , x* ⟩) (dom× p*)) (dom p))

    dom+ []ᴾ = []
    dom+ (p ∷ᴾ p*) = List.map inj₁ (dom p) ++ List.map inj₂ (dom+ p*)

  mutual
    rank : Poly G → symbols G → ℕ
    rank× : (p* : Poly* G*) → symbols× G* → ℕ
    rank+ : (p* : Poly* G*) → symbols+ G* → ℕ

    rank (poly-prod p*) = rank× p*
    rank (poly-sum p*) = rank+ p*
    rank poly-var tt = 1

    rank× []ᴾ tt = 0
    rank× (p ∷ᴾ p*) ⟨ x , x* ⟩ = rank p x + rank× p* x*

    rank+ (p ∷ᴾ p*) (inj₁ x) = rank p x
    rank+ (p ∷ᴾ p*) (inj₂ x*) = rank+ p* x*

  import PR-Trees as Trees

  -- Binary trees with signature { Leaf : 0, Branch : 2 }.
  G-Btree : Ty 1
  G-Btree = `++ [ `×× [] , `×× [ ` zero , ` zero ] ]

  Btree : Ty 0
  Btree = ind G-Btree

  G-Btree-polynomial : Poly G-Btree
  G-Btree-polynomial = poly-sum
    (poly-unit ∷ᴾ poly-pair poly-var poly-var ∷ᴾ []ᴾ)

  R-Btree : Trees.Ranked
  R-Btree = Trees.mkRanked (rank G-Btree-polynomial)

  branch-symbol : symbols G-Btree
  branch-symbol = inj₂ (inj₁ ⟨ tt , ⟨ tt , tt ⟩ ⟩)

  tree-step : {T* : Vec TY n}
    → `×× (`×× [ `×× [ U , V ] , `×× [ U , V ] ] ∷ T*)
    →ᴾ `×× (U ∷ U ∷ V ∷ V ∷ T*)
  tree-step {T* = T*} = `prod
    ⟨ C (π zero) (C (π zero) (π zero))
    , ⟨ C (π zero) (C (π (suc zero)) (π zero))
      , ⟨ C (π (suc zero)) (C (π zero) (π zero))
        , ⟨ C (π (suc zero)) (C (π (suc zero)) (π zero))
          , arrows {T* = T*} (λ i → π (suc i)) ⟩ ⟩ ⟩ ⟩

  ⟦_⟧  : Trees.PR R-Btree n → mkvec Btree n →ᴾ Btree
  ⟦_⟧* : Vec (Trees.PR R-Btree n) m → mkvec Btree n →ᴾ mkvec Btree m

  ⟦ Trees.σ (inj₁ tt) ⟧ = C roll (ι zero)
  ⟦ Trees.σ (inj₂ (inj₁ ⟨ tt , ⟨ tt , tt ⟩ ⟩)) ⟧ =
    C roll (ι (suc zero))
  ⟦ Trees.σ (inj₂ (inj₂ ())) ⟧
  ⟦ Trees.π i ⟧ = lookupᴾ i
  ⟦ Trees.C f g* ⟧ = C ⟦ f ⟧ ⟦ g* ⟧*
  ⟦ Trees.P h ⟧ = P (C
    (`case
      ⟨ C ⟦ h (inj₁ tt) ⟧ tail
      , ⟨ C ⟦ h branch-symbol ⟧ tree-step , tt ⟩ ⟩)
    dist-+-x)

  ⟦ [] ⟧*         = `prod tt
  ⟦ p ∷ p* ⟧*     = cons-prod ⟦ p ⟧ ⟦ p* ⟧*
