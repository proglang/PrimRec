\begin{code}[hide]
module PR-CCC-ind where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; [] ; _∷_; _++_; map; concat)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Vec using (Vec;[];_∷_; replicate) renaming (map to mapⱽ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ) renaming (<_,_> to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; const; flip) renaming (id to identity)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)
open import Utils

infix 6 _→ᴾ_
infix 7 _`×_
infix 8 _`+_
infix 9 _`⇒_
\end{code}
\begin{code}[hide]
Ctx = ℕ

∅ : Ctx
∅ = zero

_⁺ : Ctx → Ctx
_⁺ = suc

Structure = Ctx → Set

Var : Structure
Var = Fin


variable
  Γ : Ctx
  Δ : Ctx
  Θ : Ctx
\end{code}
\newcommand\cccDataTy{%
\begin{code}
data Ty n : Set where
  `𝟘 `𝟙   : Ty n
  _`×_ : Ty n → Ty n → Ty n
  _`+_ : Ty n → Ty n → Ty n
  _`⇒_ : Ty 0 → Ty n → Ty n
  `    : Var n → Ty n
  ind  : Ty (suc n) → Ty n
\end{code}
}
\begin{code}[hide]
TY = Ty 0

_⊢_⇒_ : Structure → Ctx → Ctx → Set
_⊢_⇒_ Trm Γ Δ = Var Γ → Trm Δ

record Mappable (Trm : Structure) : Set where
  field
    “_”   : Trm Γ → Ty Γ
    ext   : Trm ⊢ Γ ⇒ Δ → Trm ⊢ (Γ ⁺) ⇒ (Δ ⁺)
    ext-cong : ∀ {σ τ : Trm ⊢ Γ ⇒ Δ}
           → (∀ (x : Var Γ) → σ x ≡ τ x)
           → (∀ (x : Var (Γ ⁺)) → ext{Γ = Γ} σ x ≡ ext{Γ = Γ} τ x)

open Mappable {{...}} public

mapˢᴿ : ∀ {Trm : Structure}{{_ : Mappable Trm}}
  → (Trm ⊢ Γ ⇒ Δ)
    -------------------------
  → (Ty Γ → Ty Δ)

mapˢᴿ f `𝟘 = `𝟘
mapˢᴿ f `𝟙 = `𝟙
mapˢᴿ f (t₁ `× t₂) = mapˢᴿ f t₁ `× mapˢᴿ f t₂
mapˢᴿ f (t₁ `+ t₂) = mapˢᴿ f t₁ `+ mapˢᴿ f t₂
mapˢᴿ{Γ = Γ} f (t₁ `⇒ t₂) = t₁ `⇒ mapˢᴿ f t₂
mapˢᴿ f (` x) = “ f x ”
mapˢᴿ{Γ = Γ} f (ind t) = ind (mapˢᴿ (ext{Γ = Γ} f) t)

map-cong : ∀ {Trm : Structure}{{_ : Mappable Trm}}
           {σ τ : Trm ⊢ Γ ⇒ Δ}
  → (∀(x : Var Γ) → σ x ≡ τ x)
  → ∀ (ty : Ty Γ) → mapˢᴿ σ ty ≡ mapˢᴿ τ ty

map-cong eq `𝟘 = refl
map-cong eq `𝟙 = refl
map-cong eq (t₁ `× t₂) = cong₂ _`×_ (map-cong eq t₁) (map-cong eq t₂)
map-cong eq (t₁ `+ t₂) = cong₂ _`+_ (map-cong eq t₁) (map-cong eq t₂)
map-cong eq (t₁ `⇒ t₂) = cong₂ _`⇒_ refl (map-cong eq t₂)
map-cong eq (` x) = cong “_” (eq x)
map-cong eq (ind t) = cong ind (map-cong (ext-cong eq) t)

Ren : Ctx → Ctx → Set
Ren Γ Δ = Var ⊢ Γ ⇒ Δ

extᴿ : 
     Var ⊢ Γ ⇒ Δ
    --------------------------------
  →  Var ⊢ (Γ ⁺) ⇒ (Δ ⁺)

extᴿ ρ zero = zero
extᴿ ρ (suc i) = suc (ρ i)

extᴿ-cong : ∀ {r1 r2 : Ren Γ Δ}
  → (∀ (f : Var Γ) → r1 f ≡ r2 f)
  → (∀ (f : Var (Γ ⁺)) → extᴿ {Γ = Γ}{Δ = Δ} r1 f ≡ extᴿ{Γ = Γ}{Δ = Δ} r2 f)
extᴿ-cong eq (zero) = refl
extᴿ-cong eq (suc i) = cong suc (eq i)


instance
  RenameMappable : Mappable Var
  RenameMappable = record
    { “_” = ` ;
      ext = extᴿ ;
      ext-cong = extᴿ-cong
    }

ren : Ren Γ Δ → Ty Γ → Ty Δ
ren = mapˢᴿ

Sub : Ctx → Ctx → Set
Sub Γ Δ = Ty ⊢ Γ ⇒ Δ

extˢ : Sub Γ Δ → Sub (Γ ⁺) (Δ ⁺)
extˢ σ (zero) = ` zero
extˢ σ (suc i) = mapˢᴿ suc (σ i)

extˢ-cong : ∀ {s1 s2 : Sub Γ Δ}
  → (∀ (f : Var Γ) → s1 f ≡ s2 f)
  → (∀ (f : Var (Γ ⁺)) → extˢ {Γ = Γ} s1 f ≡ extˢ {Γ = Γ} s2 f )
extˢ-cong eq (zero) = refl
extˢ-cong eq (suc i) = cong (mapˢᴿ suc) (eq i)

instance
  SubstMappable : Mappable Ty
  SubstMappable = record {
    “_” = identity ;
    ext = extˢ ;
    ext-cong = extˢ-cong
    }

sub : Sub Γ Δ → Ty Γ → Ty Δ
sub = mapˢᴿ 

ids : Sub Γ Γ
ids x = ` x

push : Sub Γ Δ → Ty Δ → Sub (Γ ⁺) Δ
push σ t (zero) = t
push σ t (suc i) = σ i

σ₀ : Ty Γ → Sub (Γ ⁺) Γ
σ₀ {Γ = Γ} T = push{Γ = Γ} ids T

sub₀ : Ty ∅ → Ty (∅ ⁺) → Ty ∅
sub₀ T       = sub (σ₀ T)

infix 9 _⇐_

_⇐_ : Ty (∅ ⁺) → Ty ∅ → Ty ∅
_⇐_ G T = sub₀ T G

record Composable (T₁ T₂ T₃ : Structure)
  {{_ : Mappable T₁}} {{_ : Mappable T₂}} {{_ : Mappable T₃}} : Set₁ where
   infixr 5 _⨟_
   field
     _⨟_   : T₁ ⊢ Γ ⇒ Δ   → T₂ ⊢ Δ ⇒ Θ  →  T₃ ⊢ Γ ⇒ Θ
     ext-⨟ : ∀ (σ₁ : T₁ ⊢ Γ ⇒ Δ) → (σ₂ : T₂ ⊢ Δ ⇒ Θ)
       → ∀ (x : Var (Γ ⁺)) → (ext σ₁ ⨟ ext σ₂) x ≡ ext(σ₁ ⨟ σ₂) x 
     map-“” : ∀  (σ : T₁ ⊢ Γ ⇒ Δ) → (τ : T₂ ⊢ Δ ⇒ Θ)
       → ∀(x : Var Γ) → mapˢᴿ τ “ σ x ” ≡ “ (σ ⨟ τ) x ”

open Composable {{...}} public

map-fusion : ∀{T₁ T₂ T₃ : Structure}
   {{_ : Mappable T₁}}{{_ : Mappable T₂}}{{_ : Mappable T₃}}
   {{_ : Composable T₁ T₂ T₃}}
   → (σ : T₁ ⊢ Γ ⇒ Δ) → (τ : T₂ ⊢ Δ ⇒ Θ)
   → (ty : Ty Γ)
   → mapˢᴿ τ (mapˢᴿ σ ty) ≡ mapˢᴿ (σ ⨟ τ) ty
map-fusion σ τ `𝟘 = refl
map-fusion σ τ `𝟙 = refl
map-fusion σ τ (t₁ `× t₂) = cong₂ _`×_ (map-fusion σ τ t₁) (map-fusion σ τ t₂)
map-fusion σ τ (t₁ `+ t₂) = cong₂ _`+_ (map-fusion σ τ t₁) (map-fusion σ τ t₂)
map-fusion σ τ (t₁ `⇒ t₂) = cong₂ _`⇒_ refl (map-fusion σ τ t₂)
map-fusion σ τ (` x) = map-“” σ τ x
map-fusion σ τ (ind t) = cong ind (trans (map-fusion (ext σ) (ext τ) t) (map-cong (ext-⨟ σ τ) t))

_⨟ᴿ_ : Var ⊢ Γ ⇒ Δ → Var ⊢ Δ ⇒ Θ  →  Var ⊢ Γ ⇒ Θ
(ρ₁ ⨟ᴿ ρ₂) x = ρ₂ (ρ₁ x)

ext-⨟ᴿ : ∀ (σ : Var ⊢ Γ ⇒ Δ) (τ : Var ⊢ Δ ⇒ Θ)
  → ∀ (x : Var (Γ ⁺))
  → (extᴿ σ ⨟ᴿ extᴿ τ) x ≡ extᴿ (σ ⨟ᴿ τ) x
ext-⨟ᴿ σ τ (zero) = refl
ext-⨟ᴿ σ τ (suc i) = refl

-- The `map-“”` law is trivially proved by the relevant definitions.

instance
  RenameComposable : Composable Var Var Var
  RenameComposable = record
        { _⨟_ = _⨟ᴿ_ ;
          ext-⨟ = ext-⨟ᴿ ;
          map-“” = λ σ τ x → refl }

-- We obtain a `map-fusion` lemma for renamings, which we name `ren-ren`.

ren-ren : ∀ (σ : Var ⊢ Γ ⇒ Δ) → (τ : Var ⊢ Δ ⇒ Θ)→ ∀(ty : Ty Γ)
   → ren{Γ = Δ}{Δ = Θ} τ (ren σ ty) ≡ ren (_⨟ᴿ_{Γ = Γ}{Δ = Δ}{Θ = Θ} σ τ) ty
ren-ren σ τ ty = map-fusion σ τ ty

-- ### Substitution and renaming compose into a substitition

-- This is also straightforward to prove following the same recipe as
-- above.


_ᴿ⨟ˢ_ : Var ⊢ Γ ⇒ Δ   → Ty ⊢ Δ ⇒ Θ  →  Ty ⊢ Γ ⇒ Θ
(ρ ᴿ⨟ˢ σ) x = σ (ρ x)

ext-ᴿ⨟ˢ : (ρ : Var ⊢ Γ ⇒ Δ) (σ : Ty ⊢ Δ ⇒ Θ) → ∀(x : Var (Γ ⁺))
   → (extᴿ ρ ᴿ⨟ˢ extˢ σ) x ≡ extˢ (ρ ᴿ⨟ˢ σ) x
ext-ᴿ⨟ˢ ρ σ (zero) = refl
ext-ᴿ⨟ˢ ρ σ (suc i) = refl

instance
  RenameSubstComposable : Composable Var Ty Ty
  RenameSubstComposable = record { _⨟_ = _ᴿ⨟ˢ_ ; ext-⨟ = ext-ᴿ⨟ˢ ;
      map-“” = λ σ τ x → refl }

-- We obtain a `map-fusion` lemma for a renaming followed by
-- a substitution, which we name `ren-sub`.

ren-sub : (ρ : Var ⊢ Γ ⇒ Δ) → (τ : Ty ⊢ Δ ⇒ Θ) → ∀ (ty : Ty Γ)
   → sub{Γ = Δ} τ (ren ρ ty) ≡ sub (ρ ᴿ⨟ˢ τ) ty
ren-sub ρ τ = map-fusion ρ τ

-- ### Renaming and substitution compose into a substitution

-- The composition of a substitution followed by a renaming
-- is defined as follows, using `ren` to apply the renaming
-- to the result of `σ x`.


_ˢ⨟ᴿ_ : Ty ⊢ Γ ⇒ Δ  →  Var ⊢ Δ ⇒ Θ  →  Ty ⊢ Γ ⇒ Θ
(σ ˢ⨟ᴿ ρ) x = ren ρ (σ x)


-- The proof of the `ext-⨟` law uses the fact that two renamings compose.


ext-ˢ⨟ᴿ : (σ : Ty ⊢ Γ ⇒ Δ) (ρ : Var ⊢ Δ ⇒ Θ) → ∀(x : Var (Γ ⁺))
   → (extˢ σ ˢ⨟ᴿ extᴿ ρ) x ≡ extˢ (σ ˢ⨟ᴿ ρ) x
ext-ˢ⨟ᴿ σ ρ zero = refl
ext-ˢ⨟ᴿ {n}{m} σ ρ (suc x) =
  begin
    (extˢ σ ˢ⨟ᴿ extᴿ ρ) (suc x)
  ≡⟨ ren-ren suc (extᴿ ρ) (σ x) ⟩
    ren (ρ ⨟ᴿ suc) (σ x)
  ≡⟨ sym (ren-ren ρ suc (σ x)) ⟩
    ren suc ((σ ˢ⨟ᴿ ρ) x)
  ∎ 

-- The `map-“”` law is again trivial to prove.

instance
  SubstRenameComposable : Composable Ty Var Ty
  SubstRenameComposable = record { _⨟_ = _ˢ⨟ᴿ_ ;
      ext-⨟ = ext-ˢ⨟ᴿ; map-“” = λ σ τ x → refl }
-- We obtain a `map-fusion` lemma for a substitution followed by a
-- renaming, naming it `sub-ren`.


sub-ren : (σ : Ty ⊢ Γ ⇒ Δ) → (ρ : Var ⊢ Δ ⇒ Θ) → ∀ (ty : Ty Γ)
   → ren{Γ = Δ}{Δ = Θ} ρ (sub σ ty) ≡ sub (σ ˢ⨟ᴿ ρ) ty
sub-ren σ ρ = map-fusion σ ρ

-- ### Two substitutions compose into a substitution

-- The composition of two substitutions applies the first substitution to
-- the variable, and then applies the second substitution to the
-- resulting term using `sub`.

_ˢ⨟ˢ_ : Ty ⊢ Γ ⇒ Δ   → Ty ⊢ Δ ⇒ Θ  →  Ty ⊢ Γ ⇒ Θ
(σ ˢ⨟ˢ τ) x = sub τ (σ x)


-- The proof of the `ext-⨟` law uses the `ren-sub` and `sub-ren` lemmas.

ext-ˢ⨟ˢ :  (σ : Ty ⊢ Γ ⇒ Δ) (τ : Ty ⊢ Δ ⇒ Θ)
   → ∀(x : Var (Γ ⁺))
   → (extˢ σ ˢ⨟ˢ extˢ τ) x ≡ extˢ (σ ˢ⨟ˢ τ) x
ext-ˢ⨟ˢ σ τ zero = refl
ext-ˢ⨟ˢ σ τ  (suc x) =
  begin
    (extˢ σ ˢ⨟ˢ extˢ τ) (suc x)
  ≡⟨ ren-sub suc (extˢ τ) (σ x) ⟩
    sub (suc ᴿ⨟ˢ (extˢ τ)) (σ x)
  ≡⟨ sym (sub-ren τ suc (σ x)) ⟩
    ren suc ((σ ˢ⨟ˢ τ) x)
  ∎

-- As usual, the `map-“”` law is trivally true.


instance
  SubstComposable : Composable Ty Ty Ty
  SubstComposable = record { _⨟_ = _ˢ⨟ˢ_ ; ext-⨟ = ext-ˢ⨟ˢ ;
      map-“” = λ σ τ x → refl }

-- We obtain a `map-fusion` lemma for the composition of two
-- substitutions, naming it `sub-sub`.

sub-sub : (σ : Ty ⊢ Γ ⇒ Δ) → (τ : Ty ⊢ Δ ⇒ Θ) → ∀ (ty : Ty Γ)
   → sub τ (sub σ ty) ≡ sub (σ ˢ⨟ˢ τ) ty
sub-sub σ τ = map-fusion σ τ



subsub : (σ₁ : Sub Δ Θ) (σ₂ : Sub Γ Δ) (T : Ty Γ) → sub σ₁ (sub σ₂ T) ≡ sub ((sub σ₁) ∘ σ₂) T
subsub σ₁ σ₂ T = sub-sub σ₂ σ₁ T 



variable
  T U V W : TY
  G : Ty (∅ ⁺)
\end{code}

\begin{code}[hide]
-- interpretation
module alternative-alg where
  data Alg (⟦_⟧ᵀ : Ty 0 → Set) (G : Ty 1) : Set where
    inj : ⟦ G ⇐ ind G ⟧ᵀ → Alg ⟦_⟧ᵀ G

  {-# TERMINATING #-}
  ⟦_⟧ᵀ : TY → Set
  ⟦ `𝟘 ⟧ᵀ     = ⊥
  ⟦ `𝟙 ⟧ᵀ     = ⊤
  ⟦ T `× U ⟧ᵀ = ⟦ T ⟧ᵀ × ⟦ U ⟧ᵀ
  ⟦ T `+ U ⟧ᵀ = ⟦ T ⟧ᵀ ⊎ ⟦ U ⟧ᵀ
  ⟦ T `⇒ U ⟧ᵀ = ⟦ T ⟧ᵀ → ⟦ U ⟧ᵀ
  ⟦ ind G ⟧ᵀ  = Alg ⟦_⟧ᵀ G

\end{code}
\newcommand\cccDataAlg{%
\begin{code}
⟦_⟧ᵀ : TY → Set
{-# NO_POSITIVITY_CHECK #-}
data Alg G : Set where
  fold : ⟦ G ⇐ ind G ⟧ᵀ → Alg G 

⟦ `𝟘 ⟧ᵀ     = ⊥
⟦ `𝟙 ⟧ᵀ     = ⊤
⟦ T `× U ⟧ᵀ = ⟦ T ⟧ᵀ × ⟦ U ⟧ᵀ
⟦ T `+ U ⟧ᵀ = ⟦ T ⟧ᵀ ⊎ ⟦ U ⟧ᵀ
⟦ ind G ⟧ᵀ  = Alg G
\end{code}
}
\newcommand\cccDataAlgArrow{%
\begin{code}
⟦ T `⇒ U ⟧ᵀ = ⟦ T ⟧ᵀ → ⟦ U ⟧ᵀ
\end{code}}
\begin{code}[hide]

-- Extensional Function Equality (Homotopies)
infix 4 _~_
_~_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂}
  → (f g : (x : A) → B x) → Set _
f ~ g = ∀ x → f x ≡ g x 

extˢ~ : ∀ {σ₁ σ₂ : Sub Γ Δ}
  → σ₁ ~ σ₂
  → extˢ σ₁ ~ extˢ σ₂
extˢ~ σ₁~σ₂ zero = refl
extˢ~ σ₁~σ₂ (suc x) = cong (mapˢᴿ suc) (σ₁~σ₂ x)

sub~ : ∀ {σ₁ σ₂ : Sub Γ Δ} {t}
  → σ₁ ~ σ₂
  → sub σ₁ t ≡ sub σ₂ t
sub~ {t = `𝟘} f       = refl
sub~ {t = `𝟙} f       = refl
sub~ {t = t₁ `× t₂} f = cong₂ _`×_ (sub~ {t = t₁} f) (sub~ {t = t₂} f)
sub~ {t = t₁ `+ t₂} f = cong₂ _`+_ (sub~ {t = t₁} f) (sub~ {t = t₂} f)
sub~ {t = t₁ `⇒ t₂} f = cong₂ _`⇒_ refl (sub~ {t = t₂} f)
sub~ {t = ` x} f      = f x
sub~ {t = ind t} f    = cong ind (sub~ {t = t} (extˢ~ f))

extˢ-ids : extˢ{Γ} ids ~ ids
extˢ-ids zero    = refl
extˢ-ids (suc x) = refl

sub-ids : ∀ {n} (t : Ty n) → sub ids t ≡ t
sub-ids `𝟘         = refl
sub-ids `𝟙         = refl
sub-ids (t₁ `× t₂) = cong₂ _`×_ (sub-ids t₁) (sub-ids t₂)
sub-ids (t₁ `+ t₂) = cong₂ _`+_ (sub-ids t₁) (sub-ids t₂)
sub-ids (t₁ `⇒ t₂) = cong₂ _`⇒_ refl (sub-ids t₂)
sub-ids (` x)      = refl
sub-ids (ind t)    = cong ind (trans (sub~ {t = t} extˢ-ids)
                                     (sub-ids t))

wk-cancels-push : ∀ (σ : Sub Γ Δ) T
    → suc ᴿ⨟ˢ (push σ T) ~ σ
wk-cancels-push σ T zero    = refl
wk-cancels-push σ T (suc x) = refl

comm-⨟-σ₀ : ∀ (σ : Sub Γ Δ) T
  → (σ₀ T ˢ⨟ˢ σ) ~ (extˢ σ ˢ⨟ˢ σ₀ (sub σ T))
comm-⨟-σ₀ σ T zero = refl
comm-⨟-σ₀ σ T (suc x) =
  begin
    (σ₀ T ˢ⨟ˢ σ) (suc x)
  ≡⟨⟩
    σ x
  ≡⟨ sym (sub-ids (σ x)) ⟩
    sub ids (σ x)
  ≡⟨ sym (sub~ {t = σ x} (wk-cancels-push ids (sub σ T))) ⟩
    sub (suc ᴿ⨟ˢ (push ids (sub σ T))) (σ x)
  ≡⟨ sym (ren-sub suc (push ids (sub σ T)) (σ x)) ⟩
    sub (push ids (sub σ T)) (ren suc (σ x))
  ≡⟨⟩
    (extˢ σ ˢ⨟ˢ σ₀ (sub σ T)) (suc x)
  ∎

{-# TERMINATING #-}
\end{code}
\newcommand\cccFunFmap{%
\begin{code}
fmap : ∀ {S T : TY} (G : Ty 1)
  → (f : ⟦ S ⟧ᵀ → ⟦ T ⟧ᵀ)
  → ⟦ G ⇐ S ⟧ᵀ → ⟦ G ⇐ T ⟧ᵀ
fmap `𝟙       f tt       = tt
fmap (G `× H) f (x , y)  = fmap G f x , fmap H f y
fmap (G `+ H) f (inj₁ x) = inj₁ (fmap G f x)
fmap (G `+ H) f (inj₂ y) = inj₂ (fmap H f y)
fmap (G `⇒ H) f g        = fmap H f ∘ g
fmap (` zero) f v        = f v
\end{code}
}
\begin{code}[hide]
fmap {S}{T} (ind G) f (fold x) =
  fold (subst ⟦_⟧ᵀ (eq (σ₀ T))
        (fmap G′ f
         (subst ⟦_⟧ᵀ (sym (eq (σ₀ S))) x)))
  where
    G′ : Ty 1
    G′ = sub (σ₀ (ind G)) G
    eq : ∀ (τ : Sub 1 0) → sub τ G′ ≡ sub₀ (ind (sub (extˢ τ) G)) (sub (extˢ τ) G)
    eq τ = begin
       sub τ G′
     ≡⟨ sub-sub (σ₀ (ind G)) τ G ⟩
       sub (σ₀ (ind G) ˢ⨟ˢ τ) G
     ≡⟨ sub~ {t = G} (comm-⨟-σ₀ τ (ind G)) ⟩
       sub (extˢ τ ˢ⨟ˢ σ₀ (sub τ (ind G))) G
     ≡⟨ sym (sub-sub (extˢ τ) (σ₀ (sub τ (ind G))) G) ⟩
       sub₀ (ind (sub (extˢ τ) G)) (sub (extˢ τ) G)
     ∎

--- needs to be recursive over `ind G`
\end{code}
%% syntax of higher-order PR
\newcommand\cccPRIND{%
\begin{code}
data _→ᴾ_ : TY → TY → Set where
  id : T →ᴾ T
  C  : (f : U →ᴾ V) → (g : T →ᴾ U) → (T →ᴾ V)
  --
  `⊤ : T →ᴾ `𝟙
  `⊥ : `𝟘 →ᴾ T
  --
  `# : (f : T →ᴾ U) → (g : T →ᴾ V) → (T →ᴾ U `× V)
  π₁ : U `× V →ᴾ U
  π₂ : U `× V →ᴾ V
  --
  ι₁ : U →ᴾ U `+ V
  ι₂ : V →ᴾ U `+ V
  `case : (f : U →ᴾ T) → (g : V →ᴾ T) → U `+ V →ᴾ T
  --
  lam   : (U `× V) →ᴾ T → U →ᴾ V `⇒ T
  apply : T `⇒ U `× T →ᴾ U
  --
  fold : (G ⇐ ind G) →ᴾ ind G
  P : (h : (G ⇐ (T `× ind G)) `× U →ᴾ T) → (ind G `× U →ᴾ T)
\end{code}}
\begin{code}[hide]
  F : (h : (G ⇐ T) `× U →ᴾ T) → (ind G `× U →ᴾ T)

infix 6 _➙_
_➙_ = _→ᴾ_

\end{code}
\begin{code}[hide]
{-# TERMINATING #-}
\end{code}
\newcommand\cccFunEval{%
\begin{code}
eval : (T ➙ U) → ⟦ T ⟧ᵀ → ⟦ U ⟧ᵀ
eval `⊤       = const tt
eval id       = λ v → v
eval (C f g)  = eval f ∘ eval g
eval (`# f g) = ⟨ eval f , eval g ⟩
eval π₁       = proj₁
eval π₂       = proj₂
eval ι₁       = inj₁
eval ι₂       = inj₂
eval (`case f g) = λ{ (inj₁ x) → eval f x ; (inj₂ y) → eval g y}
eval (lam f)  = λ x y → eval f (x , y)
eval apply    = λ{ (f , x) → f x }
-- eval dist-+-x = λ{ (inj₁ x , z) → inj₁ (x , z) ; (inj₂ y , z) → inj₂ (y , z)}
eval fold     = fold
eval (P {G = G} h) = λ{ (fold x , u) → eval h ((fmap G (λ v → (eval (P h) (v , u)) , v) x) , u)}
\end{code}
}
\newcommand\cccEvalExponential{%
\begin{code}
eval (lam f)  = λ x y → eval f (x , y)
eval apply    = λ{ (f , x) → f x }
\end{code}}
\begin{code}[hide]
eval (F {G = G} h) = λ{ (fold x , u) → eval h ((fmap G (λ v → eval (F h) (v , u)) x) , u) }
\end{code}
\newcommand\cccFunVec{%
\begin{code}
vec : TY → ℕ → TY
vec T zero    = `𝟙
vec T (suc n) = T `× vec T n

lookup : (i : Fin n) → vec T n ➙ T
lookup zero    = π₁
lookup (suc i) = C (lookup i) π₂
\end{code}
}
\newcommand\cccFunAssocDist{%
\begin{code}
assoc-× : (U `× V) `× T ➙ U `× (V `× T)
assoc-× = `# (C π₁ π₁) (`# (C π₂ π₁) π₂)

unassoc-× : U `× (V `× T) ➙ (U `× V) `× T
unassoc-× = `# (`# π₁ (C π₁ π₂)) (C π₂ π₂)

comm-× : U `× V ➙ V `× U
comm-× = `# π₂ π₁

map-× : U ➙ T → V ➙ W → U `× V ➙ T `× W
map-× f g = `# (C f π₁) (C g π₂)
\end{code}
}
\begin{code}[hide]
-- laws about exponentials
exp-1 : ((U `× V) `⇒ T) `× (U `× V) ➙ T
exp-1 = apply

exp-2 : (V `⇒ (U `⇒ T)) `× (U `× V) ➙ T
exp-2 = C apply (C (C (map-× apply id) unassoc-×) (map-× id comm-×))
\end{code}
\newcommand\cccThetaDist{%
\begin{code}
theta : U ➙ V `⇒ T → U `× V ➙ T
theta g = C apply (map-× g id)

dist-+-x : (U `+ V) `× T ➙ (U `× T) `+ (V `× T)
dist-+-x = theta (`case (lam ι₁) (lam ι₂))
\end{code}}
\begin{code}
-- the exponential transpose is just lambda
tr : ∀ {A B C} → (A `× B) ➙ C → A ➙ B `⇒ C
tr r = lam r

transpose-lam : ∀ f → eval (theta{U}{V}{T} (lam f)) ≡ eval f
transpose-lam f = refl
\end{code}
\newcommand\cccExpComm{%
\begin{code}
exponential-commute : ∀ (f : (U `× V) ➙ T) → eval f ≡ eval (C apply (map-× (lam f) id))
\end{code}}
\begin{code}[hide]
exponential-commute f = refl

alpha : ∀ {A B C} → ((B `× C) `⇒ A) `× C ➙ B `⇒ A
alpha = lam (C apply (C (map-× id comm-×) assoc-×))

exp-×-1 : (U `× V) `⇒ T ➙ V `⇒ (U `⇒ T)
exp-×-1 = lam alpha

exp-×-2 : V `⇒ (U `⇒ T) ➙ (U `× V) `⇒ T
exp-×-2 = lam (C (C (C apply (map-× apply id)) unassoc-×) (map-× id comm-×))

exp-×-id : eval (C (exp-×-1{U}{V}{T}) exp-×-2) ≡ eval id
exp-×-id = refl

undist-+-× : (U `× T) `+ (V `× T) ➙ (U `+ V) `× T
undist-+-× = `case (`# (C ι₁ π₁) π₂) (`# (C ι₂ π₁) π₂)
\end{code}
\newcommand\cccEvalDistEqual{%
\begin{code}
eval-dist-+-× : ⟦ (U `+ V) `× T ⟧ᵀ → ⟦ (U `× T) `+ (V `× T) ⟧ᵀ
eval-dist-+-× = λ{ (inj₁ x , z) → inj₁ (x , z) ; (inj₂ y , z) → inj₂ (y , z)}

dist-dist′ : ∀ {U V T} → ∀ x → eval (dist-+-x{U}{V}{T}) x ≡ eval-dist-+-× x
dist-dist′ (inj₁ x , z) = refl
dist-dist′ (inj₂ y , z) = refl
\end{code}}
\begin{code}[hide]
dist-undist : ∀ {U V T} → ∀ x → eval (C (dist-+-x{U}{V}{T}) undist-+-×) x ≡ eval id x
dist-undist (inj₁ x) = refl
dist-undist (inj₂ y) = refl

undist-dist : ∀ {U V T} → ∀ x → eval (C undist-+-× (dist-+-x{U}{V}{T})) x ≡ eval id x
undist-dist (inj₁ x , z) = refl
undist-dist (inj₂ y , z) = refl

comm-+ : U `+ V ➙ V `+ U
comm-+ = `case ι₂ ι₁

assoc-+ : (U `+ V) `+ T ➙ U `+ (V `+ T)
assoc-+ = `case (`case ι₁ (C ι₂ ι₁)) (C ι₂ ι₂)

module FromNats where
\end{code}
\newcommand\cccDefGNat{%
\begin{code}
  G-Nat : Ty (∅ ⁺)
  G-Nat = `𝟙 `+ ` zero

  Nat = ind G-Nat
\end{code}
}

\begin{code}[hide]

  _ : G-Nat ⇐ Nat ≡ (`𝟙 `+ Nat)
  _ = refl

  -- zero
  _ : `𝟙 ➙ Nat
  _ = C fold ι₁

  _ : `𝟙 ➙ (`𝟙 `+ Nat)
  _ = ι₁

  -- successor
  _ : Nat ➙ Nat
  _ = C fold ι₂

  _ : Nat ➙ (`𝟙 `+ Nat)
  _ = ι₂

  import PR-Nat as Nats

\end{code}
\newcommand\cccDefNatToInd{%
\begin{code}
  ⟦_⟧  : Nats.PR n → vec Nat n ➙ Nat
  ⟦_⟧* : Vec (Nats.PR n) m → vec Nat n ➙ vec Nat m

  ⟦ Nats.Z ⟧      = C fold ι₁
  ⟦ Nats.σ ⟧      = C (C fold ι₂) π₁
  ⟦ Nats.π i ⟧    = lookup i
  ⟦ Nats.C f g* ⟧ = C ⟦ f ⟧ ⟦ g* ⟧*
  ⟦ Nats.P g h ⟧  = P (C (`case (C ⟦ g ⟧ π₂) (C ⟦ h ⟧ assoc-×)) dist-+-x)

  ⟦ [] ⟧*         = `⊤
  ⟦ p ∷ p* ⟧*     = `# ⟦ p ⟧ ⟦ p* ⟧*
\end{code}
}
\begin{code}[hide]
module FromWords where
  Alpha : Ty 0
  Alpha = `𝟙 `+ `𝟙
  G-Alpha* : Ty 1
  G-Alpha* = `𝟙 `+ (ren suc Alpha `× ` zero)

  Alpha* : Ty 0
  Alpha* = ind G-Alpha*

  ⟦_⟧ᴬ : ⟦ Alpha ⟧ᵀ → `𝟙 ➙ Alpha
  ⟦ inj₁ tt ⟧ᴬ = ι₁
  ⟦ inj₂ tt ⟧ᴬ = ι₂

  import PR-Words as Words

  ⟦_⟧  : Words.PR ⟦ Alpha ⟧ᵀ n → vec Alpha* n ➙ Alpha*
  ⟦_⟧* : Vec (Words.PR ⟦ Alpha ⟧ᵀ n) m → vec Alpha* n ➙ vec Alpha* m

  ⟦ Words.Z ⟧ = C (C fold ι₁) `⊤
  ⟦ Words.σ a ⟧ = C (C fold (C ι₂ (`# (C ⟦ a ⟧ᴬ `⊤) id))) π₁
  ⟦ Words.π i ⟧ = lookup i
  ⟦ Words.C f g* ⟧ = C ⟦ f ⟧ ⟦ g* ⟧*
  ⟦ Words.P g h ⟧ = P (C (`case (C ⟦ g ⟧ π₂) (C (C (C (`case (C ⟦ h (inj₁ tt) ⟧ assoc-×) (C ⟦ h (inj₂ tt) ⟧ assoc-×)) dist-+-x) (`# (C (`case (C ι₁ π₂) (C ι₂ π₂)) π₁) π₂)) (`# (C dist-+-x π₁) π₂))) dist-+-x)

  ⟦ [] ⟧*         = `⊤
  ⟦ p ∷ p* ⟧*     = `# ⟦ p ⟧ ⟦ p* ⟧*

module FromTrees where
  -- generic stuff
  symbols : (G : Ty 1) → Set
  symbols G = ⟦ G ⇐ `𝟙 ⟧ᵀ

  data Poly : Ty 1 → Set where
    poly-unit : Poly `𝟙
    poly-pair : ∀ {G}{H} → Poly G → Poly H → Poly (G `× H)
    poly-sum  : ∀ {G}{H} → Poly G → Poly H → Poly (G `+ H)
    poly-var  : Poly (` zero)

  -- enumerate symbols
  dom : ∀ {G} → Poly G → List (symbols G)
  dom poly-unit = tt ∷ []
  dom (poly-pair pg ph) = concat (map (λ g → map (λ h → g , h) (dom ph)) (dom pg))
  dom (poly-sum pg ph) = map inj₁ (dom pg) ++ map inj₂ (dom ph)
  dom poly-var = tt ∷ []

  rank : ∀ {G} → Poly G → symbols G → ℕ
  rank poly-unit tt = 0
  rank (poly-pair pg ph) (gs , hs) = rank pg gs + rank ph hs 
  rank (poly-sum pg ph) (inj₁ gs) = rank pg gs
  rank (poly-sum pg ph) (inj₂ hs) = rank ph hs
  rank poly-var tt = 1

  import PR-Trees as Trees

  -- binary trees with signature { Leaf:0, Branch:2 }
  G-Btree : Ty 1
  G-Btree = `𝟙 `+ (` zero `× ` zero)

  Btree : Ty 0
  Btree = ind G-Btree

  G-Btree-polynomial : Poly G-Btree
  G-Btree-polynomial = poly-sum poly-unit (poly-pair poly-var poly-var)

  R-Btree : Trees.Ranked
  R-Btree = Trees.mkRanked (rank G-Btree-polynomial)

  ⟦_⟧  : Trees.PR R-Btree n → vec Btree n ➙ Btree
  ⟦_⟧* : Vec (Trees.PR R-Btree n) m → vec Btree n ➙ vec Btree m

  ⟦ Trees.σ (inj₁ tt) ⟧ = C fold ι₁
  ⟦ Trees.σ (inj₂ (tt , tt)) ⟧ = C fold (C ι₂ (`# π₁ (C π₁ π₂)))
  ⟦ Trees.π i ⟧ = lookup i
  ⟦ Trees.C f g* ⟧ = C ⟦ f ⟧ ⟦ g* ⟧*
  ⟦ Trees.P h ⟧ = P (C (`case (C ⟦ h (inj₁ tt) ⟧ π₂)
                              (C ⟦ h (inj₂ (tt , tt)) ⟧ (`# (C π₁ (C π₁ π₁)) (`# (C π₂ (C π₁ π₁)) (`# (C π₁ (C π₂ π₁)) (`# (C π₂ (C π₂ π₁)) π₂))))))
                       dist-+-x)
  
  ⟦ [] ⟧*         = `⊤
  ⟦ p ∷ p* ⟧*     = `# ⟦ p ⟧ ⟦ p* ⟧*
\end{code}
\begin{code}[hide]
module FromCC where
  import PR-CC-ind as CC

  -- translation of types

  T⟦_⟧ : CC.Ty n → Ty n
  T⟦ CC.`𝟘 ⟧ = `𝟘
  T⟦ CC.`𝟙 ⟧ = `𝟙
  T⟦ T₁ CC.`× T₂ ⟧ = T⟦ T₁ ⟧ `× T⟦ T₂ ⟧
  T⟦ T₁ CC.`+ T₂ ⟧ = T⟦ T₁ ⟧ `+ T⟦ T₂ ⟧
  T⟦ CC.` x ⟧ = ` x
  T⟦ CC.ind T ⟧ = ind T⟦ T ⟧

  -- translation of types is compatible with substitution

  postulate
    extensionality : ∀ {A B : Set} {f g : A → B}
      → (∀ (x : A) → f x ≡ g x)
        -----------------------
      → f ≡ g

  lemma-ren : ∀ (ρ : CC.Ren Γ Δ) → ∀ x → ext ρ x ≡ CC.ext ρ x
  lemma-ren ρ zero = refl
  lemma-ren ρ (suc x) = refl

  trans-compat-ren : ∀ (ρ : CC.Ren Γ Δ) (T : CC.Ty Γ) → ren ρ T⟦ T ⟧ ≡ T⟦ CC.ren ρ T ⟧
  trans-compat-ren ρ CC.`𝟘 = refl
  trans-compat-ren ρ CC.`𝟙 = refl
  trans-compat-ren ρ (T₁ CC.`× T₂) = cong₂ _`×_ (trans-compat-ren ρ T₁) (trans-compat-ren ρ T₂)
  trans-compat-ren ρ (T₁ CC.`+ T₂) = cong₂ _`+_ (trans-compat-ren ρ T₁) (trans-compat-ren ρ T₂)
  trans-compat-ren ρ (CC.` x) = refl
  trans-compat-ren ρ (CC.ind T) = cong ind (trans (trans-compat-ren (extᴿ ρ) T) 
                                                  (cong (λ hole → T⟦ CC.ren hole T ⟧) (extensionality (lemma-ren ρ))) )

  trans-compat-ext : ∀ (σ : CC.Sub Γ Δ) x → T⟦ CC.extˢ σ x ⟧ ≡ extˢ (T⟦_⟧ ∘ σ) x
  trans-compat-ext σ zero = refl
  trans-compat-ext σ (suc x) = sym (trans-compat-ren suc (σ x))

  trans-compat-subst : ∀ (G : CC.Ty Γ) (σ : CC.Sub Γ Δ) → T⟦ CC.sub σ G ⟧ ≡ sub (T⟦_⟧ ∘ σ) T⟦ G ⟧
  trans-compat-subst CC.`𝟘 σ = refl
  trans-compat-subst CC.`𝟙 σ = refl
  trans-compat-subst (G₁ CC.`× G₂) σ = cong₂ _`×_ (trans-compat-subst G₁ σ) (trans-compat-subst G₂ σ)
  trans-compat-subst (G₁ CC.`+ G₂) σ = cong₂ _`+_ (trans-compat-subst G₁ σ) (trans-compat-subst G₂ σ)
  trans-compat-subst (CC.` x) σ = refl
  trans-compat-subst (CC.ind G) σ = cong ind (trans (trans-compat-subst G (CC.extˢ σ))
                                                    (cong (λ hole → sub hole T⟦ G ⟧) (extensionality (trans-compat-ext σ))))

  trans-compat-lemma : ∀ (T : CC.Ty Γ) x → T⟦ CC.σ₀ T x ⟧ ≡ σ₀ T⟦ T ⟧ x
  trans-compat-lemma T zero = refl
  trans-compat-lemma T (suc x) = refl

  trans-compat-subst0 : ∀ G T → T⟦ G CC.⇐ T ⟧ ≡ T⟦ G ⟧ ⇐ T⟦ T ⟧
  -- there should be a more direct proof along the lines of the case for `CC.ind G`
  -- trans-compat-subst0 G T = trans (trans-compat-subst G (CC.σ₀ T)) {!trans (cong sub!}
  trans-compat-subst0 CC.`𝟘 T = refl
  trans-compat-subst0 CC.`𝟙 T = refl
  trans-compat-subst0 (G₁ CC.`× G₂) T rewrite trans-compat-subst0 G₁ T | trans-compat-subst0 G₂ T = refl
  trans-compat-subst0 (G₁ CC.`+ G₂) T rewrite trans-compat-subst0 G₁ T | trans-compat-subst0 G₂ T = refl
  trans-compat-subst0 (CC.` zero) T = refl
  trans-compat-subst0 (CC.ind G) T = cong ind (trans (trans-compat-subst G (CC.extˢ (CC.σ₀ T)))
                                                     (cong (λ hole → sub hole T⟦ G ⟧)
                                                           (extensionality (λ x → trans (trans-compat-ext (CC.σ₀ T) x)
                                                                                        (cong (λ hole → extˢ hole x)
                                                                                              (extensionality (trans-compat-lemma T)))))))


  -- translation of types preserves meaning

  record _≅_ A B : Set where
    field
      from : A → B
      to   : B → A
      to∘from : ∀ (x : A) → to (from x) ≡ x
      from∘to : ∀ (y : B) → from (to y) ≡ y

  id-≅ : ∀ {A} → A ≅ A
  id-≅ = record { from = λ x → x ; to = λ y → y ; to∘from = λ x → refl ; from∘to = λ y → refl }
  open _≅_

  from-fmap : (G : CC.Ty 1) (H : CC.Ty 1) → (∀ T → CC.⟦ T ⟧ᵀ → ⟦ T⟦ T ⟧ ⟧ᵀ) → (CC.⟦ G CC.⇐ CC.ind H ⟧ᵀ → ⟦ T⟦ G ⟧ ⇐ ind T⟦ H ⟧ ⟧ᵀ)
  from-fmap CC.`𝟙 H f tt = tt
  from-fmap (G₁ CC.`× G₂) H f (x₁ , x₂) = (from-fmap G₁ H f x₁) , (from-fmap G₂ H f x₂)
  from-fmap (G₁ CC.`+ G₂) H f (inj₁ x) = inj₁ (from-fmap G₁ H f x)
  from-fmap (G₁ CC.`+ G₂) H f (inj₂ y) = inj₂ (from-fmap G₂ H f y)
  from-fmap (CC.` zero) H f x = f (CC.ind H) x
  from-fmap (CC.ind G) H f (CC.fold x) =
    let from-x = subst CC.⟦_⟧ᵀ (from-eq (CC.σ₀ (CC.ind H))) in
    fold (subst ⟦_⟧ᵀ (to-eq (σ₀ (ind (T⟦ H ⟧))))
          (from-fmap G′ H f
           {!x  !}) )
    where
      G′ : CC.Ty 1
      G′ = CC.sub (CC.σ₀ (CC.ind G)) G
      to-eq : ∀ (τ : Sub 1 0) → sub τ (T⟦ G′ ⟧) ≡ sub₀ (ind (sub (extˢ τ) (T⟦ G ⟧))) (sub (extˢ τ) (T⟦ G ⟧))
      to-eq τ = begin
          sub τ (T⟦ G′ ⟧)
        ≡⟨ cong (sub τ) (trans-compat-subst G (CC.σ₀ (CC.ind G))) ⟩
          sub τ (sub (T⟦_⟧ ∘ CC.σ₀ (CC.ind G)) T⟦ G ⟧)
        ≡⟨ sub-sub (T⟦_⟧ ∘ (CC.σ₀ (CC.ind G))) τ T⟦ G ⟧ ⟩
          sub ((T⟦_⟧ ∘ CC.σ₀ (CC.ind G)) ˢ⨟ˢ τ) T⟦ G ⟧
        ≡⟨ {!sub~ {t = T⟦ G ⟧} !} ⟩
          {!!}
      from-eq : ∀ (τ : CC.Sub 1 0) → CC.sub τ G′ ≡ CC.sub₀ (CC.ind (CC.sub (CC.extˢ τ) G)) (CC.sub (CC.extˢ τ) G)
      from-eq = {!!}
      

  to-fmap : (G : CC.Ty 1) (H : CC.Ty 1) → (∀ T → ⟦ T⟦ T ⟧ ⟧ᵀ → CC.⟦ T ⟧ᵀ) → (⟦ T⟦ G ⟧ ⇐ ind T⟦ H ⟧ ⟧ᵀ → CC.⟦ G CC.⇐ CC.ind H ⟧ᵀ)
  to-fmap CC.`𝟙 H f tt = tt
  to-fmap (G₁ CC.`× G₂) H f (x₁ , x₂) = (to-fmap G₁ H f x₁) , (to-fmap G₂ H f x₂)
  to-fmap (G₁ CC.`+ G₂) H f (inj₁ x) = inj₁ (to-fmap G₁ H f x)
  to-fmap (G₁ CC.`+ G₂) H f (inj₂ y) = inj₂ (to-fmap G₂ H f y)
  to-fmap (CC.` zero) H f x = f (CC.ind H) x
  to-fmap (CC.ind G) H f (fold x) = CC.fold {!!}

  {-# TERMINATING #-}
  from-T : ∀ (T : CC.TY) → CC.⟦ T ⟧ᵀ → ⟦ T⟦ T ⟧ ⟧ᵀ
  to-T : ∀ (T : CC.TY) → ⟦ T⟦ T ⟧ ⟧ᵀ → CC.⟦ T ⟧ᵀ

  from-T CC.`𝟙 tt = tt
  from-T (T₁ CC.`× T₂) (x , y) = (from-T T₁ x) , (from-T T₂ y)
  from-T (T₁ CC.`+ T₂) (inj₁ x) = inj₁ (from-T T₁ x)
  from-T (T₁ CC.`+ T₂) (inj₂ y) = inj₂ (from-T T₂ y)
  from-T (CC.ind G) (CC.fold x) = fold (from-fmap G G from-T x)

  to-T CC.`𝟙 tt = tt
  to-T (T₁ CC.`× T₂) (x , y) = (to-T T₁ x) , (to-T T₂ y)
  to-T (T₁ CC.`+ T₂) (inj₁ x) = inj₁ (to-T T₁ x)
  to-T (T₁ CC.`+ T₂) (inj₂ y) = inj₂ (to-T T₂ y)
  to-T (CC.ind G) (fold x) = CC.fold (to-fmap G G to-T x)

  to∘from-T : ∀ (T : CC.TY) → ∀ x → to-T T (from-T T x) ≡ x
  to∘from-fmap-T : ∀ (G H : CC.Ty 1) → ∀ x → to-fmap G H to-T (from-fmap G H from-T x) ≡ x

  to∘from-T CC.`𝟙 x = refl
  to∘from-T (T₁ CC.`× T₂) (x₁ , x₂) = cong₂ _,_ (to∘from-T T₁ x₁) (to∘from-T T₂ x₂)
  to∘from-T (T₁ CC.`+ T₂) (inj₁ x) = cong inj₁ (to∘from-T T₁ x)
  to∘from-T (T₁ CC.`+ T₂) (inj₂ y) = cong inj₂ (to∘from-T T₂ y)
  to∘from-T (CC.ind G) (CC.fold x) = cong CC.fold (to∘from-fmap-T G G x)

  to∘from-fmap-T CC.`𝟙 H tt = refl
  to∘from-fmap-T (G₁ CC.`× G₂) H (x₁ , x₂) = cong₂ _,_ (to∘from-fmap-T G₁ H x₁) (to∘from-fmap-T G₂ H x₂)
  to∘from-fmap-T (G₁ CC.`+ G₂) H (inj₁ x) = cong inj₁ (to∘from-fmap-T G₁ H x)
  to∘from-fmap-T (G₁ CC.`+ G₂) H (inj₂ y) = cong inj₂ (to∘from-fmap-T G₂ H y)
  to∘from-fmap-T (CC.` zero) H x = to∘from-T (CC.ind H) x
  to∘from-fmap-T (CC.ind G) H (CC.fold x) = cong CC.fold {!!}

  from∘to-T : ∀ (T : CC.TY) → ∀ x → from-T T (to-T T x) ≡ x
  from∘to-fmap-T : ∀ (G H : CC.Ty 1) → ∀ x → from-fmap G H from-T (to-fmap G H to-T x) ≡ x

  from∘to-T T x = {!!}
  from∘to-fmap-T G H x = {!!}

  type-trans-preserves : ∀ (T : CC.TY) → CC.⟦ T ⟧ᵀ ≅ ⟦ T⟦ T ⟧ ⟧ᵀ
  type-trans-preserves T =
    record {
      from = from-T T ;
      to = to-T T ;
      to∘from = to∘from-T T ;
      from∘to = from∘to-T T }

  {-
  type-trans-preserves : ∀ (T : CC.TY) → CC.⟦ T ⟧ᵀ ≅ ⟦ T⟦ T ⟧ ⟧ᵀ
  type-alg-preserves : ∀ (G : CC.Ty 1) → CC.Alg G ≅ Alg T⟦ G ⟧

  type-trans-preserves CC.`𝟘 = id-≅
  type-trans-preserves CC.`𝟙 = id-≅
  type-trans-preserves (T₁ CC.`× T₂)
    with type-trans-preserves T₁ | type-trans-preserves T₂
  ... | T₁-≅ | T₂-≅ = record { from = λ{ (fst , snd) → from T₁-≅ fst , from T₂-≅ snd} ;
                               to = λ (x₁ , x₂) → (to T₁-≅ x₁) , (to T₂-≅ x₂) ;
                               to∘from = λ (x₁ , x₂) → cong₂ _,_ (to∘from T₁-≅ x₁) (to∘from T₂-≅ x₂) ;
                               from∘to = λ (x₁ , x₂) → cong₂ _,_ (from∘to T₁-≅ x₁) (from∘to T₂-≅ x₂)}
  type-trans-preserves (T₁ CC.`+ T₂)
    with type-trans-preserves T₁ | type-trans-preserves T₂
  ... | T₁-≅ | T₂-≅ = record { from = λ{ (inj₁ x) → inj₁ (from T₁-≅ x) ; (inj₂ y) → inj₂ (from T₂-≅ y)} ;
                              to = λ{ (inj₁ x) → inj₁ (to T₁-≅ x) ; (inj₂ y) → inj₂ (to T₂-≅ y)} ;
                              to∘from = λ{ (inj₁ x) → cong inj₁ (to∘from T₁-≅ x) ; (inj₂ y) → cong inj₂ (to∘from T₂-≅ y)} ;
                              from∘to = λ{ (inj₁ x) → cong inj₁ (from∘to T₁-≅ x) ; (inj₂ y) → cong inj₂ (from∘to T₂-≅ y)} }
  type-trans-preserves (CC.ind G) = {!!}

  -- not sure how this can work
  type-alg-preserves G = {!!}
  -}

  -- translation of arrows

  E⟦_⟧ : ∀ {T U : CC.TY} → T CC.→ᴾ U → T⟦ T ⟧ →ᴾ T⟦ U ⟧
  E⟦ CC.id ⟧ = id
  E⟦ CC.C p₁ p₂ ⟧ = C E⟦ p₁ ⟧ E⟦ p₂ ⟧
  E⟦ CC.`⊤ ⟧ = `⊤
  E⟦ CC.`⊥ ⟧ = `⊥
  E⟦ CC.`# p₁ p₂ ⟧ = `# E⟦ p₁ ⟧ E⟦ p₂ ⟧
  E⟦ CC.π₁ ⟧ = π₁
  E⟦ CC.π₂ ⟧ = π₂
  E⟦ CC.ι₁ ⟧ = ι₁
  E⟦ CC.ι₂ ⟧ = ι₂
  E⟦ CC.`case p₁ p₂ ⟧ = `case E⟦ p₁ ⟧ E⟦ p₂ ⟧
  E⟦ CC.dist-+-x ⟧ = dist-+-x
  E⟦ CC.fold{G = G} ⟧
    rewrite trans-compat-subst0 G (CC.ind G) = fold
  E⟦ CC.P{G = G}{T = T} p ⟧
    with E⟦ p ⟧
  ... | Ep
    rewrite trans-compat-subst0 G (T CC.`× CC.ind G) = P Ep
  E⟦ CC.F{G = G}{T = T} p ⟧
    with E⟦ p ⟧
  ... | Ep
    rewrite trans-compat-subst0 G T = F Ep

  -- translation preserves semantics

  trans-preserves : ∀ {T U : CC.TY} → (p : T CC.→ᴾ U)
    → let T-≅ = type-trans-preserves T in
      let U-≅ = type-trans-preserves U in
    ∀ x → from U-≅ (CC.eval p x) ≡ eval E⟦ p ⟧ (from T-≅ x)
  trans-preserves CC.id x = refl
  trans-preserves (CC.C p₁ p₂) x
    rewrite trans-preserves p₁ (CC.eval p₂ x)
          | trans-preserves p₂ x = refl
  trans-preserves CC.`⊤ x = refl
  trans-preserves (CC.`# p₁ p₂) x
    rewrite trans-preserves p₁ x
          | trans-preserves p₂ x = refl
  trans-preserves CC.π₁ x = refl
  trans-preserves CC.π₂ x = refl
  trans-preserves CC.ι₁ x = refl
  trans-preserves CC.ι₂ x = refl
  trans-preserves (CC.`case p₁ p₂) (inj₁ x) = trans-preserves p₁ x
  trans-preserves (CC.`case p₁ p₂) (inj₂ y) = trans-preserves p₂ y
  trans-preserves CC.dist-+-x x = {!!}
  trans-preserves CC.fold x = {!!}
  trans-preserves (CC.P p) x = {!!}
  trans-preserves (CC.F p) x = {!!}
\end{code}
