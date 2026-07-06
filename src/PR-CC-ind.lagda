\begin{code}[hide]
module PR-CC-ind where


open import Data.Fin using (Fin; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; [] ; _∷_; _++_; map; concat)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Vec using (Vec;[];_∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂) renaming (<_,_> to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; const) renaming (id to identity)
import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Utils


infix 6 _→ᴾ_
infix 7 _`×_
infix 8 _`+_

module Harper where
\end{code}
\newcommand\ccHarper{%
\begin{code}
  data PolyOp : Set where
    `𝕏 `𝟙   : PolyOp
    _`×_ : PolyOp → PolyOp → PolyOp
    _`+_ : PolyOp → PolyOp → PolyOp

  data Ty : Set where
    `𝟘 `𝟙 : Ty
    _`×_ : Ty → Ty → Ty
    _`+_ : Ty → Ty → Ty
    ind  : PolyOp → Ty 
\end{code}}
\newcommand\ccDataTy{%
\begin{code}

data Ty n :  Set where
  `𝟘 `𝟙   : Ty n
  _`×_ : Ty n → Ty n → Ty n
  _`+_ : Ty n → Ty n → Ty n
  `    : Fin n → Ty n
  ind  : Ty (suc n) → Ty n

TY = Ty 0
\end{code}
}
\begin{code}[hide]


_⊢_⇒_ : (ℕ → Set) → ℕ → ℕ → Set
_⊢_⇒_ Trm n m = Fin n → Trm m


record Mappable (Trm : ℕ → Set) : Set where
  field “_”  : ∀{n} → Trm n → Ty n
  field ext : ∀ {n m} → Trm ⊢ n ⇒ m → Trm ⊢ (suc n) ⇒ (suc m)
  field ext-cong : ∀{n m}{σ τ : Trm ⊢ n ⇒ m} → (∀ (x : Fin n) → σ x ≡ τ x) → (∀(x : Fin (suc n)) → ext {n} σ x ≡ ext {n} τ x)


open Mappable {{...}} public


mapˢᴿ : ∀ {n m}{Trm}{{_ : Mappable Trm}}
  → (Trm ⊢ n ⇒ m)
    -------------------------
  → (Ty n → Ty m)
mapˢᴿ f `𝟘 = `𝟘
mapˢᴿ f `𝟙 = `𝟙
mapˢᴿ f (tyA `× tyB) = mapˢᴿ f tyA `× mapˢᴿ f tyB
mapˢᴿ f (tyA `+ tyB) = (mapˢᴿ f tyA) `+ (mapˢᴿ f tyB)
mapˢᴿ f (` x) = “ (f x) ”
mapˢᴿ {n'}{m} f (ind ty) = ind (mapˢᴿ (ext {n = n'} f)  ty)


map-cong : ∀{n m}{T}{{_ : Mappable T}}{σ τ : T ⊢ n ⇒ m}
  → (∀(x : Fin n) → σ x ≡ τ x)
  → ∀(ty : Ty n)
  → mapˢᴿ σ ty ≡ mapˢᴿ τ ty
map-cong eq `𝟘 = refl
map-cong eq `𝟙 = refl
map-cong {n} {m} {T} eq (tyA `× tyB) = cong₂ _`×_ (map-cong {n} {m} {T} eq tyA) (map-cong {n} {m} {T} eq tyB)
map-cong  {n} {m} {T} eq (tyA `+ tyB) = cong₂ _`+_ (map-cong {n} {m} {T} eq tyA) (map-cong {n} {m} {T} eq tyB)
map-cong eq (` x) = cong “_” (eq x)
map-cong eq (ind ty) = cong ind (map-cong (ext-cong eq) ty)


Ren : ℕ → ℕ → Set
Ren n m = Fin ⊢ n ⇒ m

extᴿ : ∀ {n m} → (Fin ⊢ n ⇒ m)
    --------------------------------
  →  Fin ⊢ (suc n) ⇒ (suc m)
extᴿ ρ zero      =  zero
extᴿ ρ (suc x)  =  suc (ρ x)

extᴿ-cong : ∀ {n m} {r1 r2 : Ren n m} → (∀ (f : Fin n) → r1 f ≡ r2 f) → (∀ (f : Fin (suc n)) → extᴿ {n} r1 f ≡ extᴿ {n} r2 f )
extᴿ-cong {n} {m} {r1} {r2} eq zero = refl
extᴿ-cong {n} {m} {r1} {r2} eq (suc f) = cong suc (eq f)

instance
  RenameMappable : Mappable Fin
  RenameMappable = record { “_” = ` ; ext = extᴿ ; ext-cong = extᴿ-cong  }


ren : Ren n m → Ty n → Ty m
ren = mapˢᴿ

Sub : ℕ → ℕ → Set
Sub n m = Ty ⊢ n ⇒ m

extˢ : ∀ {n m} → Sub n m → Sub (suc n) (suc m)
extˢ σ zero    = ` zero
extˢ σ (suc x) =  mapˢᴿ  (suc) (σ x) 


extˢ-cong : ∀ {n m} {s1 s2 : Sub n m} → (∀ (f : Fin n) → s1 f ≡ s2 f) → (∀ (f : Fin (suc n)) → extˢ {n} s1 f ≡ extˢ {n} s2 f )
extˢ-cong {n} {m} {s1} {s2} eq zero = refl
extˢ-cong {n} {m} {s1} {s2} eq (suc f) = cong (mapˢᴿ suc) (eq f) -- cong (ren suc) (eq f)

instance
  SubstMappable : Mappable Ty
  SubstMappable = record { “_” = identity ; ext = extˢ ; ext-cong = extˢ-cong  }

sub : Sub n m → Ty n → Ty m
sub = mapˢᴿ 

idₛ : Sub n n
idₛ x = ` x

_,ₛ_ : Sub m n → Ty n → Sub (suc m) n
(σ ,ₛ t) zero    = t
(σ ,ₛ t) (suc x) = σ x

σ₀ : Ty n → Sub (suc n) n
σ₀ T = idₛ ,ₛ T

sub₀ : Ty n → Ty (suc n) → Ty n
sub₀ T       = sub (σ₀ T)

infix 9 _⇐_

_⇐_ : Ty (suc n) → Ty n → Ty n
_⇐_ G T = sub₀ T G

record Composable (T₁ T₂ T₃ : ℕ → Set)
   {{_ : Mappable T₁}} {{_ : Mappable T₂}} {{_ : Mappable T₃}} : Set₁ where
   infixr 5 _⨟_
   field _⨟_ : ∀{n m o} → T₁ ⊢ n ⇒ m   → T₂ ⊢ m ⇒ o  →  T₃ ⊢ n ⇒ o
   
   field ext-⨟ : ∀{n m o} → (σ₁ : T₁ ⊢ n ⇒ m) →  (σ₂ : T₂ ⊢ m ⇒ o) → ∀(x : Fin (suc n)) → (ext σ₁ ⨟ ext σ₂) x ≡ ext (σ₁ ⨟ σ₂) x
   field map-“” : ∀{n m o} → (σ : T₁ ⊢ n ⇒ m) → (τ : T₂ ⊢ m ⇒ o) → ∀(x : Fin n) → mapˢᴿ τ “ σ x ” ≡ “ (σ ⨟ τ) x ”

open Composable {{...}} public

map-fusion : ∀ {n m o}{T₁ T₂ T₃}
   {{_ : Mappable T₁}}{{_ : Mappable T₂}}{{_ : Mappable T₃}}
   {{_ : Composable T₁ T₂ T₃}}
   → (σ : T₁ ⊢ n ⇒ m) → (τ : T₂ ⊢ m ⇒ o) →  (ty : Ty n)
   → mapˢᴿ τ (mapˢᴿ σ ty) ≡ mapˢᴿ (σ ⨟ τ) ty
map-fusion σ τ `𝟘 = refl
map-fusion σ τ `𝟙 = refl
map-fusion σ τ (tyA `× tyB) rewrite map-fusion σ τ tyA  | map-fusion σ τ tyB = refl
map-fusion σ τ (tyA `+ tyB) rewrite map-fusion σ τ tyA  | map-fusion σ τ tyB = refl
map-fusion σ τ (` x) rewrite map-“”  σ τ x = refl
map-fusion σ τ (ind ty) rewrite map-fusion (ext σ) (ext τ) ty | map-cong (ext-⨟ σ τ) ty = cong ind refl



_⨟ᴿ_ : ∀{n m o} → Fin ⊢ n ⇒ m   → Fin ⊢ m ⇒ o  →  Fin ⊢ n ⇒ o
(ρ₁ ⨟ᴿ ρ₂) x = ρ₂ (ρ₁ x)



-- ```
ext-⨟ᴿ : ∀{n m o} (σ : Fin ⊢ n ⇒ m) (τ : Fin ⊢ m ⇒ o) → ∀ (x : Fin (suc n))
   → (extᴿ σ ⨟ᴿ extᴿ τ) x ≡ extᴿ (σ ⨟ᴿ τ) x
ext-⨟ᴿ {n} {m} {o} σ τ zero = refl
ext-⨟ᴿ {n} {m} {o} σ τ (suc x) = refl
-- ```

-- The `map-“”` law is trivially proved by the relevant definitions.

-- ```
instance
  RenameComposable : Composable Fin Fin Fin
  RenameComposable = record { _⨟_ = _⨟ᴿ_ ; ext-⨟ = ext-⨟ᴿ ;
      map-“” = λ σ τ x → refl }
-- ```

-- We obtain a `map-fusion` lemma for renamings, which we name `ren-ren`.

-- ```
ren-ren : ∀ {n m o} → (σ : Fin ⊢ n ⇒ m) → (τ : Fin ⊢ m ⇒ o)→ ∀(ty : Ty n)
   → ren τ (ren σ ty) ≡ ren (σ ⨟ᴿ τ) ty
ren-ren σ τ ty = map-fusion σ τ ty
-- ```

-- ### Substitution and renaming compose into a substitition

-- This is also straightforward to prove following the same recipe as
-- above.

-- ```
_ᴿ⨟ˢ_ : ∀{n m o} → Fin ⊢ n ⇒ m   → Ty ⊢ m ⇒ o  →  Ty ⊢ n ⇒ o
(ρ ᴿ⨟ˢ σ) x = σ (ρ x)

ext-ᴿ⨟ˢ : ∀{n m o} (ρ : Fin ⊢ n ⇒ m) (σ : Ty ⊢ m ⇒ o) → ∀(x : Fin (suc n))
   → (extᴿ ρ ᴿ⨟ˢ extˢ σ) x ≡ extˢ (ρ ᴿ⨟ˢ σ) x
ext-ᴿ⨟ˢ ρ σ zero = refl
ext-ᴿ⨟ˢ ρ σ  (suc x) = refl

instance
  RenameSubstComposable : Composable Fin Ty Ty
  RenameSubstComposable = record { _⨟_ = _ᴿ⨟ˢ_ ; ext-⨟ = ext-ᴿ⨟ˢ ;
      map-“” = λ σ τ x → refl }
-- ```

-- We obtain a `map-fusion` lemma for a renaming followed by
-- a substitution, which we name `ren-sub`.

-- ```
ren-sub : ∀ {n m o} → (ρ : Fin ⊢ n ⇒ m) → (τ : Ty ⊢ m ⇒ o) → ∀ (ty : Ty n)
   → sub τ (ren ρ ty) ≡ sub (ρ ᴿ⨟ˢ τ) ty
ren-sub ρ τ = map-fusion ρ τ
-- ```

-- ### Renaming and substitution compose into a substitution

-- The composition of a substitution followed by a renaming
-- is defined as follows, using `ren` to apply the renaming
-- to the result of `σ x`.

-- ```
_ˢ⨟ᴿ_ : ∀{n m o} →  Ty ⊢ n ⇒ m  →  Fin ⊢ m ⇒ o  →  Ty ⊢ n ⇒ o
(σ ˢ⨟ᴿ ρ) x = ren ρ (σ x)
-- ```

-- The proof of the `ext-⨟` law uses the fact that two renamings compose.

-- ```
ext-ˢ⨟ᴿ : ∀{n m o} (σ : Ty ⊢ n ⇒ m) (ρ : Fin ⊢ m ⇒ o) → ∀(x : Fin (suc n))
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
-- ```

-- The `map-“”` law is again trivial to prove.

-- ```
instance
  SubstRenameComposable : Composable Ty Fin Ty
  SubstRenameComposable = record { _⨟_ = _ˢ⨟ᴿ_ ;
      ext-⨟ = ext-ˢ⨟ᴿ; map-“” = λ σ τ x → refl }
-- ```

-- We obtain a `map-fusion` lemma for a substitution followed by a
-- renaming, naming it `sub-ren`.

-- ```
sub-ren : ∀ {n m o} → (σ : Ty ⊢ n ⇒ m) → (ρ : Fin ⊢ m ⇒ o) → ∀ (ty : Ty n)
   → ren ρ (sub σ ty) ≡ sub (σ ˢ⨟ᴿ ρ) ty
sub-ren σ ρ = map-fusion σ ρ
-- ```

-- ### Two substitutions compose into a substitution

-- The composition of two substitutions applies the first substitution to
-- the variable, and then applies the second substitution to the
-- resulting term using `sub`.

-- ```
_ˢ⨟ˢ_ : ∀{n m o} → Ty ⊢ n ⇒ m   → Ty ⊢ m ⇒ o  →  Ty ⊢ n ⇒ o
(σ ˢ⨟ˢ τ) x = sub τ (σ x)
-- ```

-- The proof of the `ext-⨟` law uses the `ren-sub` and `sub-ren` lemmas.

-- ```
ext-ˢ⨟ˢ : ∀{n m o} (σ : Ty ⊢ n ⇒ m) (τ : Ty ⊢ m ⇒ o)
   → ∀(x : Fin (suc n))
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
-- ```

-- As usual, the `map-“”` law is trivally true.

-- ```
instance
  SubstComposable : Composable Ty Ty Ty
  SubstComposable = record { _⨟_ = _ˢ⨟ˢ_ ; ext-⨟ = ext-ˢ⨟ˢ ;
      map-“” = λ σ τ x → refl }
-- ```

-- We obtain a `map-fusion` lemma for the composition of two
-- substitutions, naming it `sub-sub`.

-- ```
sub-sub : ∀ {n m o} → (σ : Ty ⊢ n ⇒ m) → (τ : Ty ⊢ m ⇒ o) → ∀ (ty : Ty n)
   → sub τ (sub σ ty) ≡ sub (σ ˢ⨟ˢ τ) ty
sub-sub σ τ = map-fusion σ τ



subsub : (σ₁ : Sub m o) (σ₂ : Sub n m) (T : Ty n) → sub σ₁ (sub σ₂ T) ≡ sub ((sub σ₁) ∘ σ₂) T
subsub σ₁ σ₂ T = sub-sub σ₂ σ₁ T 



variable
  T U V : TY
  G : Ty 1
\end{code}
\newcommand\ccDataPR{%
\begin{code}
data _→ᴾ_ : TY → TY → Set where
  -- category
  id : T →ᴾ T
  C  : (f : U →ᴾ V) → (g : T →ᴾ U) → (T →ᴾ V)
  -- initial, terminal
  `⊤ : T →ᴾ `𝟙
  `⊥ : `𝟘 →ᴾ T
  -- product, introduction and elimination
  `# : (f : T →ᴾ U) → (g : T →ᴾ V) → (T →ᴾ U `× V)
  π₁ : U `× V →ᴾ U
  π₂ : U `× V →ᴾ V
  -- sum, introduction and elimination
  ι₁ : U →ᴾ U `+ V
  ι₂ : V →ᴾ U `+ V
  `case : (f : U →ᴾ T) → (g : V →ᴾ T) → U `+ V →ᴾ T
  -- distributivity
  dist-+-x : (U `+ V) `× T →ᴾ (U `× T) `+ (V `× T)
  -- inductive, introduction and elimination
  con : (G ⇐ ind G) →ᴾ ind G
  Pr : (h : (G ⇐ (T `× ind G)) `× U →ᴾ T) → (ind G `× U →ᴾ T)
\end{code}
}
\newcommand\ccDataPRF{%
\begin{code}
  Ct : (h : (G ⇐ T) `× U →ᴾ T) → (ind G `× U →ᴾ T)
\end{code}
}
\begin{code}[hide]
-- interpretation
\end{code}
\newcommand\ccDataAlg{%
\begin{code}
⟦_⟧ᵀ : TY → Set

data Alg (G : Ty 1) : Set where
  con : ⟦ G ⇐ ind G ⟧ᵀ → Alg G 

⟦ `𝟘 ⟧ᵀ     = ⊥
⟦ `𝟙 ⟧ᵀ     = ⊤
⟦ T `× U ⟧ᵀ = ⟦ T ⟧ᵀ × ⟦ U ⟧ᵀ
⟦ T `+ U ⟧ᵀ = ⟦ T ⟧ᵀ ⊎ ⟦ U ⟧ᵀ
⟦ ind G ⟧ᵀ  = Alg G
\end{code}
}
\begin{code}[hide]

-- Extensional Function Equality (Homotopies)
infix 4 _~_
_~_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂}
  → (f g : (x : A) → B x) → Set _
f ~ g = ∀ x → f x ≡ g x 

extˢ~ : ∀ {m n} {σ₁ σ₂ : Sub m n}
  → σ₁ ~ σ₂
  → extˢ σ₁ ~ extˢ σ₂
extˢ~ σ₁~σ₂ zero = refl
extˢ~ σ₁~σ₂ (suc x) = cong (mapˢᴿ suc) (σ₁~σ₂ x)

sub~ : ∀ {m n} {σ₁ σ₂ : Sub m n} {t}
  → σ₁ ~ σ₂
  → sub σ₁ t ≡ sub σ₂ t
sub~ {t = `𝟘} f       = refl
sub~ {t = `𝟙} f       = refl
sub~ {t = t₁ `× t₂} f = cong₂ _`×_ (sub~ {t = t₁} f) (sub~ {t = t₂} f)
sub~ {t = t₁ `+ t₂} f = cong₂ _`+_ (sub~ {t = t₁} f) (sub~ {t = t₂} f)
sub~ {t = ` x} f      = f x
sub~ {t = ind t} f    = cong ind (sub~ {t = t} (extˢ~ f))

extˢ-idₛ : ∀ {n} → extˢ (idₛ {n}) ~ idₛ
extˢ-idₛ zero    = refl
extˢ-idₛ (suc x) = refl

sub-idₛ : ∀ {n} (t : Ty n) → sub idₛ t ≡ t
sub-idₛ `𝟘         = refl
sub-idₛ `𝟙         = refl
sub-idₛ (t₁ `× t₂) = cong₂ _`×_ (sub-idₛ t₁) (sub-idₛ t₂)
sub-idₛ (t₁ `+ t₂) = cong₂ _`+_ (sub-idₛ t₁) (sub-idₛ t₂)
sub-idₛ (` x)      = refl
sub-idₛ (ind t)    = cong ind (trans (sub~ {t = t} extˢ-idₛ)
                                     (sub-idₛ t))

wk-cancels-,ₛ : ∀ {m n} (σ : Sub m n) T
    → suc ᴿ⨟ˢ (σ ,ₛ T) ~ σ
wk-cancels-,ₛ σ T zero    = refl
wk-cancels-,ₛ σ T (suc x) = refl

comm-⨟-σ₀ : ∀ {n m} (σ : Sub m n) T
  → (σ₀ T ˢ⨟ˢ σ) ~ (extˢ σ ˢ⨟ˢ σ₀ (sub σ T))
comm-⨟-σ₀ σ T zero = refl
comm-⨟-σ₀ σ T (suc x) =
  begin
    (σ₀ T ˢ⨟ˢ σ) (suc x)
  ≡⟨⟩
    σ x
  ≡⟨ sym (sub-idₛ (σ x)) ⟩
    sub idₛ (σ x)
  ≡⟨ sym (sub~ {t = σ x} (wk-cancels-,ₛ idₛ (sub σ T))) ⟩
    sub (suc ᴿ⨟ˢ (idₛ ,ₛ sub σ T)) (σ x)
  ≡⟨ sym (ren-sub suc (idₛ ,ₛ sub σ T) (σ x)) ⟩
    sub (idₛ ,ₛ sub σ T) (ren suc (σ x))
  ≡⟨⟩
    (extˢ σ ˢ⨟ˢ σ₀ (sub σ T)) (suc x)
  ∎
\end{code}
\newcommand\ccEqUnfold{
\begin{code}
eq-unfold : ∀ (τ : Sub 1 0) (H : Ty 2)
  → sub τ (H ⇐ ind H)  ≡  sub (extˢ τ) H ⇐ ind (sub (extˢ τ) H)
\end{code}
}
\begin{code}[hide]
eq-unfold τ H = begin
   sub τ (H ⇐ ind H)
 ≡⟨ sub-sub (σ₀ (ind H)) τ H ⟩
   sub (σ₀ (ind H) ˢ⨟ˢ τ) H
 ≡⟨ sub~ {t = H} (comm-⨟-σ₀ τ (ind H)) ⟩
   sub (extˢ τ ˢ⨟ˢ σ₀ (sub τ (ind H))) H
 ≡⟨ sym (sub-sub (extˢ τ) (σ₀ (sub τ (ind H))) H) ⟩
   sub₀ (ind (sub (extˢ τ) H)) (sub (extˢ τ) H)
 ∎

\end{code}
\newcommand\ccFunFmapSignature{%
\begin{code}
fmap : ∀ {S T : TY} (G : Ty 1)
  → (f : ⟦ S ⟧ᵀ → ⟦ T ⟧ᵀ)
  → ⟦ G ⇐ S ⟧ᵀ → ⟦ G ⇐ T ⟧ᵀ
\end{code}}
\newcommand\ccFunFmap{%
\begin{code}
fmap `𝟘       f ()
fmap `𝟙       f tt       = tt
fmap (G `× H) f (x , y)  = fmap G f x , fmap H f y
fmap (G `+ H) f (inj₁ x) = inj₁ (fmap G f x)
fmap (G `+ H) f (inj₂ y) = inj₂ (fmap H f y)
fmap (` zero) f v        = f v
\end{code}
}
\newcommand\ccFunFmapInd{
\begin{code}
fmap {S}{T} (ind H) f (con x)
  rewrite sym (eq-unfold (σ₀ S) H)
  with fmap (H ⇐ ind H) f x
... | ih
  rewrite eq-unfold (σ₀ T) H =
  con ih
\end{code}
}
\begin{code}[hide]
{-# TERMINATING #-}
\end{code}
\newcommand\ccFunEval{%
\begin{code}
eval : (T →ᴾ U) → ⟦ T ⟧ᵀ → ⟦ U ⟧ᵀ
eval `⊥        = λ()
eval `⊤        = const tt
eval id        = λ v → v
eval (C f g)   = eval f ∘ eval g
eval (`# f g) = ⟨ eval f , eval g ⟩
eval π₁        = proj₁
eval π₂        = proj₂
eval ι₁        = inj₁
eval ι₂        = inj₂
eval (`case f g) = λ{ (inj₁ x) → eval f x ; (inj₂ y) → eval g y}
eval dist-+-x = λ{ (inj₁ x , z) → inj₁ (x , z) ; (inj₂ y , z) → inj₂ (y , z)}
eval con     = con
eval (Pr {G = G} h) = λ{ (con x , u) → eval h ((fmap G (λ v → (eval (Pr h) (v , u)) , v) x) , u)}
\end{code}
}
\begin{code}[hide]
eval (Ct {G = G} h) = λ{ (con x , u) → eval h ((fmap G (λ v → eval (Ct h) (v , u)) x) , u) }
\end{code}
\newcommand\ccFunMkvec{%
\begin{code}
vec : TY → ℕ → TY
vec T zero    = `𝟙
vec T (suc n) = T `× vec T n

lookup : (i : Fin n) → vec T n →ᴾ T
lookup zero    = π₁
lookup (suc i) = C (lookup i) π₂
\end{code}
}
\newcommand\ccFunAssocDist{%
\begin{code}
assoc-× : (U `× V) `× T →ᴾ U `× (V `× T)
assoc-× = `# (C π₁ π₁) (`# (C π₂ π₁) π₂)

undist-+-× : (U `× T) `+ (V `× T) →ᴾ (U `+ V) `× T
undist-+-× = `case (`# (C ι₁ π₁) π₂) (`# (C ι₂ π₁) π₂)
\end{code}
}
\begin{code}[hide]
unassoc-× : U `× (V `× T) →ᴾ (U `× V) `× T
unassoc-× = `# (`# π₁ (C π₁ π₂)) (C π₂ π₂)

comm-× : U `× V →ᴾ V `× U
comm-× = `# π₂ π₁

comm-+ : U `+ V →ᴾ V `+ U
comm-+ = `case ι₂ ι₁

assoc-+ : (U `+ V) `+ T →ᴾ U `+ (V `+ T)
assoc-+ = `case (`case ι₁ (C ι₂ ι₁)) (C ι₂ ι₂)

unassoc-+ : U `+ (V `+ T) →ᴾ (U `+ V) `+ T
unassoc-+ = `case (C ι₁ ι₁) (`case (C ι₁ ι₂) ι₂)

unit-left-× : (`𝟙 `× T) →ᴾ T
unit-left-× = π₂

unit-right-× : (T `× `𝟙) →ᴾ T
unit-right-× = π₁

unit-left-+ : (`𝟘 `+ T) →ᴾ T
unit-left-+ = `case `⊥ id

unit-right-+ : (T `+ `𝟘) →ᴾ T
unit-right-+ = `case id `⊥

𝟘→𝟙₁ :
\end{code}
\newcommand\ccZeroOne{
\begin{code}[inline]
  `𝟘 →ᴾ `𝟙
\end{code}
}
\begin{code}[hide]
𝟘→𝟙₁ = `⊤

𝟘→𝟙₂ : `𝟘 →ᴾ `𝟙
𝟘→𝟙₂ = `⊥

-- mp : T →ᴾ U → G ⇐ T →ᴾ G ⇐ U
-- mp {G = `𝟘} h = id
-- mp {G = `𝟙} h = id
-- mp {G = G₁ `× G₂} h = `# (C (mp {G = G₁} h) π₁) (C (mp {G = G₂} h) π₂)
-- mp {G = G₁ `+ G₂} h = `case (C ι₁ (mp {G = G₁} h)) (C ι₂ (mp {G = G₂} h))
-- mp {G = ` zero} h = h
-- mp {G = ind G} h = C con (C (Ct {!!}) (`# id `⊤))

-- f : (h : (G ⇐ T) `× U →ᴾ T) → (ind G `× U →ᴾ T)
-- f h = Pr {!!}

-- p : (h : (G ⇐ (T `× ind G)) `× U →ᴾ T) → (ind G `× U →ᴾ T)
-- p {G = G} h = C π₁ (Ct (`# h (C con (C (mp {G = G} π₂) π₁))))

module FromNats where
\end{code}
\newcommand\ccDefGNat{%
\begin{code}
  G-Nat : Ty 1
  G-Nat = `𝟙 `+ ` zero

  Nat = ind G-Nat
\end{code}
}

\begin{code}[hide]

  _ : G-Nat ⇐ Nat ≡ (`𝟙 `+ Nat)
  _ = refl

  -- zero
  _ : `𝟙 →ᴾ Nat
  _ = C con ι₁

  _ : `𝟙 →ᴾ (`𝟙 `+ Nat)
  _ = ι₁

  -- successor
  _ : Nat →ᴾ Nat
  _ = C con ι₂

  _ : Nat →ᴾ (`𝟙 `+ Nat)
  _ = ι₂

  import PR-Nat as Nats

\end{code}
\newcommand\ccDefNatToInd{%
\begin{code}
  ⟦_⟧  : Nats.PR n → vec Nat n →ᴾ Nat
  ⟦_⟧* : Vec (Nats.PR n) m → vec Nat n →ᴾ vec Nat m

  ⟦ [] ⟧*         = `⊤
  ⟦ p ∷ p* ⟧*     = `# ⟦ p ⟧ ⟦ p* ⟧*

  ⟦ Nats.Z ⟧      = C con ι₁
  ⟦ Nats.σ ⟧      = C (C con ι₂) π₁
  ⟦ Nats.π i ⟧    = lookup i
  ⟦ Nats.C f g* ⟧ = C ⟦ f ⟧ ⟦ g* ⟧*
  ⟦ Nats.Pr g h ⟧  = Pr (C (`case (C ⟦ g ⟧ π₂) (C ⟦ h ⟧ assoc-×)) dist-+-x)
\end{code}
}
\begin{code}[hide]
  ⟦ Nats.Ct g h ⟧  = Ct (C (`case (C ⟦ g ⟧ π₂) ⟦ h ⟧) dist-+-x)

module FromWords where
  Alpha : Ty 0
  Alpha = `𝟙 `+ `𝟙
  G-Alpha* : Ty 1
  G-Alpha* = `𝟙 `+ (ren suc Alpha `× ` zero)

  Alpha* : Ty 0
  Alpha* = ind G-Alpha*

  ⟦_⟧ᴬ : ⟦ Alpha ⟧ᵀ → `𝟙 →ᴾ Alpha
  ⟦ inj₁ tt ⟧ᴬ = ι₁
  ⟦ inj₂ tt ⟧ᴬ = ι₂

  import PR-Words as Words

  ⟦_⟧  : Words.PR ⟦ Alpha ⟧ᵀ n → vec Alpha* n →ᴾ Alpha*
  ⟦_⟧* : Vec (Words.PR ⟦ Alpha ⟧ᵀ n) m → vec Alpha* n →ᴾ vec Alpha* m

  ⟦ Words.Z ⟧ = C (C con ι₁) `⊤
  ⟦ Words.σ a ⟧ = C (C con (C ι₂ (`# (C ⟦ a ⟧ᴬ `⊤) id))) π₁
  ⟦ Words.π i ⟧ = lookup i
  ⟦ Words.C f g* ⟧ = C ⟦ f ⟧ ⟦ g* ⟧*
  ⟦ Words.Pr g h ⟧ = Pr (C (`case (C ⟦ g ⟧ π₂) (C (C (C (`case (C ⟦ h (inj₁ tt) ⟧ assoc-×) (C ⟦ h (inj₂ tt) ⟧ assoc-×)) dist-+-x) (`# (C (`case (C ι₁ π₂) (C ι₂ π₂)) π₁) π₂)) (`# (C dist-+-x π₁) π₂))) dist-+-x)

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

  ⟦_⟧  : Trees.PR R-Btree n → vec Btree n →ᴾ Btree
  ⟦_⟧* : Vec (Trees.PR R-Btree n) m → vec Btree n →ᴾ vec Btree m

  ⟦ Trees.σ (inj₁ tt) ⟧ = C con ι₁
  ⟦ Trees.σ (inj₂ (tt , tt)) ⟧ = C con (C ι₂ (`# π₁ (C π₁ π₂)))
  ⟦ Trees.π i ⟧ = lookup i
  ⟦ Trees.C f g* ⟧ = C ⟦ f ⟧ ⟦ g* ⟧*
  ⟦ Trees.Pr h ⟧ = Pr (C (`case (C ⟦ h (inj₁ tt) ⟧ π₂)
                              (C ⟦ h (inj₂ (tt , tt)) ⟧ (`# (C π₁ (C π₁ π₁)) (`# (C π₂ (C π₁ π₁)) (`# (C π₁ (C π₂ π₁)) (`# (C π₂ (C π₂ π₁)) π₂))))))
                       dist-+-x)
  
  ⟦ [] ⟧*         = `⊤
  ⟦ p ∷ p* ⟧*     = `# ⟦ p ⟧ ⟦ p* ⟧*
\end{code}
