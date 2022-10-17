{-# OPTIONS --rewriting  #-}

module PR-CC-Ctx where


open import Data.Fin using (Fin; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; [] ; _∷_; _++_; map; concat)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Vec using (Vec;[];_∷_;lookup)
open import Data.Product using (_×_; _,_; proj₁; proj₂) renaming (<_,_> to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; const) renaming (id to identity)
import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)
open import Utils
open import HVec
open import Agda.Builtin.Equality.Rewrite


import PR-CC-ind as PF


-- infix 6 _→ᴾ_
infix 7 _`×_
infix 8 _`+_


data Ty n :  Set where
  `𝟙   : Ty n
  _`×_ : Ty n → Ty n → Ty n
  _`+_ : Ty n → Ty n → Ty n
  `    : Fin n → Ty n
  ind  : Ty (suc n) → Ty n
  _⇒_ : Ty n → Ty n → Ty n 

TY = Ty 0



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
mapˢᴿ f `𝟙 = `𝟙
mapˢᴿ f (tyA `× tyB) = mapˢᴿ f tyA `× mapˢᴿ f tyB
mapˢᴿ f (tyA `+ tyB) = (mapˢᴿ f tyA) `+ (mapˢᴿ f tyB)
mapˢᴿ f (` x) = “ (f x) ”
mapˢᴿ {n'}{m} f (ind ty) = ind (mapˢᴿ (ext {n = n'} f)  ty)
mapˢᴿ eq (tyA ⇒ tyB) = mapˢᴿ eq tyA ⇒ mapˢᴿ eq tyB

map-cong : ∀{n m}{T}{{_ : Mappable T}}{σ τ : T ⊢ n ⇒ m}
  → (∀(x : Fin n) → σ x ≡ τ x)
  → ∀(ty : Ty n)
  → mapˢᴿ σ ty ≡ mapˢᴿ τ ty
map-cong eq `𝟙 = refl
map-cong {n} {m} {T} eq (tyA `× tyB) = cong₂ _`×_ (map-cong {n} {m} {T} eq tyA) (map-cong {n} {m} {T} eq tyB)
map-cong  {n} {m} {T} eq (tyA `+ tyB) = cong₂ _`+_ (map-cong {n} {m} {T} eq tyA) (map-cong {n} {m} {T} eq tyB)
map-cong eq (` x) = cong “_” (eq x)
map-cong eq (ind ty) = cong ind (map-cong (ext-cong eq) ty)
map-cong eq (tyA ⇒ tyB) = cong₂ _⇒_ (map-cong eq tyA) (map-cong eq tyB)

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

sub₀ : Ty 0 → Ty 1 → Ty 0
sub₀ T       = sub (σ₀ T)


-- record Composable (T₁ T₂ T₃ : ℕ → Set)
--    {{_ : Mappable T₁}} {{_ : Mappable T₂}} {{_ : Mappable T₃}} : Set₁ where
--    infixr 5 _⨟_
--    field _⨟_ : ∀{n m o} → T₁ ⊢ n ⇒ m   → T₂ ⊢ m ⇒ o  →  T₃ ⊢ n ⇒ o
   
--    field ext-⨟ : ∀{n m o} → (σ₁ : T₁ ⊢ n ⇒ m) →  (σ₂ : T₂ ⊢ m ⇒ o) → ∀(x : Fin (suc n)) → (ext σ₁ ⨟ ext σ₂) x ≡ ext (σ₁ ⨟ σ₂) x
--    field map-“” : ∀{n m o} → (σ : T₁ ⊢ n ⇒ m) → (τ : T₂ ⊢ m ⇒ o) → ∀(x : Fin n) → mapˢᴿ τ “ σ x ” ≡ “ (σ ⨟ τ) x ”

-- open Composable {{...}} public

-- -- map-fusionˢ = {!   !}


-- map-fusion : ∀ {n m o}{T₁ T₂ T₃}
--    {{_ : Mappable T₁}}{{_ : Mappable T₂}}{{_ : Mappable T₃}}
--    {{_ : Composable T₁ T₂ T₃}}
--    → (σ : T₁ ⊢ n ⇒ m) → (τ : T₂ ⊢ m ⇒ o) →  (ty : Ty n)
--    → mapˢᴿ τ (mapˢᴿ σ ty) ≡ mapˢᴿ (σ ⨟ τ) ty
-- map-fusion σ τ `𝟙 = refl
-- map-fusion σ τ (tyA `× tyB) rewrite map-fusion σ τ tyA  | map-fusion σ τ tyB = refl
-- map-fusion σ τ (tyA `+ tyB) rewrite map-fusion σ τ tyA  | map-fusion σ τ tyB = refl
-- map-fusion σ τ (` x) rewrite map-“”  σ τ x = refl
-- map-fusion σ τ (ind ty) rewrite map-fusion (ext σ) (ext τ) ty | map-cong (ext-⨟ σ τ) ty = cong ind refl



-- _⨟ᴿ_ : ∀{n m o} → Fin ⊢ n ⇒ m   → Fin ⊢ m ⇒ o  →  Fin ⊢ n ⇒ o
-- (ρ₁ ⨟ᴿ ρ₂) x = ρ₂ (ρ₁ x)



-- -- ```
-- ext-⨟ᴿ : ∀{n m o} (σ : Fin ⊢ n ⇒ m) (τ : Fin ⊢ m ⇒ o) → ∀ (x : Fin (suc n))
--    → (extᴿ σ ⨟ᴿ extᴿ τ) x ≡ extᴿ (σ ⨟ᴿ τ) x
-- ext-⨟ᴿ {n} {m} {o} σ τ zero = refl
-- ext-⨟ᴿ {n} {m} {o} σ τ (suc x) = refl
-- -- ```

-- -- The `map-“”` law is trivially proved by the relevant definitions.

-- -- ```
-- instance
--   RenameComposable : Composable Fin Fin Fin
--   RenameComposable = record { _⨟_ = _⨟ᴿ_ ; ext-⨟ = ext-⨟ᴿ ;
--       map-“” = λ σ τ x → refl }
-- -- ```

-- -- We obtain a `map-fusion` lemma for renamings, which we name `ren-ren`.

-- -- ```
-- ren-ren : ∀ {n m o} → (σ : Fin ⊢ n ⇒ m) → (τ : Fin ⊢ m ⇒ o)→ ∀(ty : Ty n)
--    → ren τ (ren σ ty) ≡ ren (σ ⨟ᴿ τ) ty
-- ren-ren σ τ ty = map-fusion σ τ ty
-- -- ```

-- -- ### Substitution and renaming compose into a substitition

-- -- This is also straightforward to prove following the same recipe as
-- -- above.

-- -- ```
-- _ᴿ⨟ˢ_ : ∀{n m o} → Fin ⊢ n ⇒ m   → Ty ⊢ m ⇒ o  →  Ty ⊢ n ⇒ o
-- (ρ ᴿ⨟ˢ σ) x = σ (ρ x)

-- ext-ᴿ⨟ˢ : ∀{n m o} (ρ : Fin ⊢ n ⇒ m) (σ : Ty ⊢ m ⇒ o) → ∀(x : Fin (suc n))
--    → (extᴿ ρ ᴿ⨟ˢ extˢ σ) x ≡ extˢ (ρ ᴿ⨟ˢ σ) x
-- ext-ᴿ⨟ˢ ρ σ zero = refl
-- ext-ᴿ⨟ˢ ρ σ  (suc x) = refl

-- instance
--   RenameSubstComposable : Composable Fin Ty Ty
--   RenameSubstComposable = record { _⨟_ = _ᴿ⨟ˢ_ ; ext-⨟ = ext-ᴿ⨟ˢ ;
--       map-“” = λ σ τ x → refl }
-- -- ```

-- -- We obtain a `map-fusion` lemma for a renaming followed by
-- -- a substitution, which we name `ren-sub`.

-- -- ```
-- ren-sub : ∀ {n m o} → (ρ : Fin ⊢ n ⇒ m) → (τ : Ty ⊢ m ⇒ o) → ∀ (ty : Ty n)
--    → sub τ (ren ρ ty) ≡ sub (ρ ᴿ⨟ˢ τ) ty
-- ren-sub ρ τ = map-fusion ρ τ
-- -- ```

-- -- ### Renaming and substitution compose into a substitution

-- -- The composition of a substitution followed by a renaming
-- -- is defined as follows, using `ren` to apply the renaming
-- -- to the result of `σ x`.

-- -- ```
-- _ˢ⨟ᴿ_ : ∀{n m o} →  Ty ⊢ n ⇒ m  →  Fin ⊢ m ⇒ o  →  Ty ⊢ n ⇒ o
-- (σ ˢ⨟ᴿ ρ) x = ren ρ (σ x)
-- -- ```

-- -- The proof of the `ext-⨟` law uses the fact that two renamings compose.

-- -- ```
-- ext-ˢ⨟ᴿ : ∀{n m o} (σ : Ty ⊢ n ⇒ m) (ρ : Fin ⊢ m ⇒ o) → ∀(x : Fin (suc n))
--    → (extˢ σ ˢ⨟ᴿ extᴿ ρ) x ≡ extˢ (σ ˢ⨟ᴿ ρ) x
-- ext-ˢ⨟ᴿ σ ρ zero = refl
-- ext-ˢ⨟ᴿ {n}{m} σ ρ (suc x) =
--   begin
--     (extˢ σ ˢ⨟ᴿ extᴿ ρ) (suc x)
--   ≡⟨ ren-ren suc (extᴿ ρ) (σ x) ⟩
--     ren (ρ ⨟ᴿ suc) (σ x)
--   ≡⟨ sym (ren-ren ρ suc (σ x)) ⟩
--     ren suc ((σ ˢ⨟ᴿ ρ) x)
--   ∎ 
-- -- ```

-- -- The `map-“”` law is again trivial to prove.

-- -- ```
-- instance
--   SubstRenameComposable : Composable Ty Fin Ty
--   SubstRenameComposable = record { _⨟_ = _ˢ⨟ᴿ_ ;
--       ext-⨟ = ext-ˢ⨟ᴿ; map-“” = λ σ τ x → refl }
-- -- ```

-- -- We obtain a `map-fusion` lemma for a substitution followed by a
-- -- renaming, naming it `sub-ren`.

-- -- ```
-- sub-ren : ∀ {n m o} → (σ : Ty ⊢ n ⇒ m) → (ρ : Fin ⊢ m ⇒ o) → ∀ (ty : Ty n)
--    → ren ρ (sub σ ty) ≡ sub (σ ˢ⨟ᴿ ρ) ty
-- sub-ren σ ρ = map-fusion σ ρ
-- -- ```

-- -- ### Two substitutions compose into a substitution

-- -- The composition of two substitutions applies the first substitution to
-- -- the variable, and then applies the second substitution to the
-- -- resulting term using `sub`.

-- -- ```
-- _ˢ⨟ˢ_ : ∀{n m o} → Ty ⊢ n ⇒ m   → Ty ⊢ m ⇒ o  →  Ty ⊢ n ⇒ o
-- (σ ˢ⨟ˢ τ) x = sub τ (σ x)
-- -- ```

-- -- The proof of the `ext-⨟` law uses the `ren-sub` and `sub-ren` lemmas.

-- -- ```
-- ext-ˢ⨟ˢ : ∀{n m o} (σ : Ty ⊢ n ⇒ m) (τ : Ty ⊢ m ⇒ o)
--    → ∀(x : Fin (suc n))
--    → (extˢ σ ˢ⨟ˢ extˢ τ) x ≡ extˢ (σ ˢ⨟ˢ τ) x
-- ext-ˢ⨟ˢ σ τ zero = refl
-- ext-ˢ⨟ˢ σ τ  (suc x) =
--   begin
--     (extˢ σ ˢ⨟ˢ extˢ τ) (suc x)
--   ≡⟨ ren-sub suc (extˢ τ) (σ x) ⟩
--     sub (suc ᴿ⨟ˢ (extˢ τ)) (σ x)
--   ≡⟨ sym (sub-ren τ suc (σ x)) ⟩
--     ren suc ((σ ˢ⨟ˢ τ) x)
--   ∎
-- -- ```

-- -- As usual, the `map-“”` law is trivally true.

-- -- ```
-- instance
--   SubstComposable : Composable Ty Ty Ty
--   SubstComposable = record { _⨟_ = _ˢ⨟ˢ_ ; ext-⨟ = ext-ˢ⨟ˢ ;
--       map-“” = λ σ τ x → refl }
-- -- ```

-- -- We obtain a `map-fusion` lemma for the composition of two
-- -- substitutions, naming it `sub-sub`.

-- -- ```
-- sub-sub : ∀ {n m o} → (σ : Ty ⊢ n ⇒ m) → (τ : Ty ⊢ m ⇒ o) → ∀ (ty : Ty n)
--    → sub τ (sub σ ty) ≡ sub (σ ˢ⨟ˢ τ) ty
-- sub-sub σ τ = map-fusion σ τ



-- subsub : (σ₁ : Sub m o) (σ₂ : Sub n m) (T : Ty n) → sub σ₁ (sub σ₂ T) ≡ sub ((sub σ₁) ∘ σ₂) T
-- subsub σ₁ σ₂ T = sub-sub σ₂ σ₁ T 




variable
  T U V : TY
  G : Ty 1



Ctx : ℕ → Set
Ctx n = Vec TY n

data Exp : ∀ {n : ℕ} → Ctx n → TY → Set where
  `0 :  ∀ {n : ℕ} {ctx : Ctx n} → Exp ctx ( `𝟙)
  App  : ∀ {n : ℕ} {ctx : Ctx n} {tyA tyB} →   Exp ctx (tyA ⇒ tyB) → Exp ctx tyA → Exp ctx tyB
  Var : ∀ {n : ℕ} {ctx : Ctx n}  → (f : Fin n) → Exp ctx (lookup ctx f)
  Lam  : ∀ {n : ℕ} {ctx : Ctx n} { tyA tyB} → Exp (tyA ∷ ctx) tyB → Exp ctx  (tyA ⇒ tyB)


--   --
  `# : ∀ {n : ℕ} {ctx : Ctx n} { tyA tyB} → Exp ctx tyA → Exp ctx tyB → Exp ctx (tyA `× tyB)
  π₁ : ∀ {n : ℕ} {ctx : Ctx n} → Exp ctx (U `× V) → Exp ctx  U
  π₂ : ∀ {n : ℕ} {ctx : Ctx n} → Exp ctx (U `× V) → Exp ctx  V
--   --
  ι₁ :  ∀ {n : ℕ} {ctx : Ctx n} →  Exp ctx U → Exp ctx (U `+ V)
  ι₂ : ∀ {n : ℕ} {ctx : Ctx n} → Exp ctx V → Exp ctx (U `+ V)
  `case : ∀ {n : ℕ} {ctx : Ctx n} {tyA tyB tyC : TY} →  Exp ctx (tyA `+ tyB) → Exp (tyA ∷ ctx) (tyC) → Exp (tyB ∷ ctx) (tyC) → Exp (ctx) (tyC)
--   --
--   fold : sub₀ (ind G) G →ᴾ ind G
--   P : (h : sub₀ (T `× ind G) G `× U →ᴾ T) → (ind G `× U →ᴾ T)

--   F : (h : sub₀ T G `× U →ᴾ T) → (ind G `× U →ᴾ T)

-- interpretation


⟦_⟧ᵀ : TY → Set

data Alg (G : Ty 1) : Set where
  fold : ⟦ sub₀ (ind G) G ⟧ᵀ → Alg G 

⟦ `𝟙 ⟧ᵀ     = ⊤
⟦ T `× U ⟧ᵀ = ⟦ T ⟧ᵀ × ⟦ U ⟧ᵀ
⟦ T `+ U ⟧ᵀ = ⟦ T ⟧ᵀ ⊎ ⟦ U ⟧ᵀ
⟦ ind G ⟧ᵀ  = {!   !} -- Alg G
⟦ tyA ⇒ tyB ⟧ᵀ = ⟦ tyA ⟧ᵀ  →  ⟦ tyB ⟧ᵀ
-- \end{code}
-- }
-- \begin{code}[hide]

-- -- Extensional Function Equality (Homotopies)
-- infix 4 _~_
-- _~_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂}
--   → (f g : (x : A) → B x) → Set _
-- f ~ g = ∀ x → f x ≡ g x 

-- extˢ~ : ∀ {m n} {σ₁ σ₂ : Sub m n}
--   → σ₁ ~ σ₂
--   → extˢ σ₁ ~ extˢ σ₂
-- extˢ~ σ₁~σ₂ zero = refl
-- extˢ~ σ₁~σ₂ (suc x) = cong (mapˢᴿ suc) (σ₁~σ₂ x)

-- sub~ : ∀ {m n} {σ₁ σ₂ : Sub m n} {t}
--   → σ₁ ~ σ₂
--   → sub σ₁ t ≡ sub σ₂ t
-- sub~ {t = `𝟙} f       = refl
-- sub~ {t = t₁ `× t₂} f = cong₂ _`×_ (sub~ {t = t₁} f) (sub~ {t = t₂} f)
-- sub~ {t = t₁ `+ t₂} f = cong₂ _`+_ (sub~ {t = t₁} f) (sub~ {t = t₂} f)
-- sub~ {t = ` x} f      = f x
-- sub~ {t = ind t} f    = cong ind (sub~ {t = t} (extˢ~ f))

-- extˢ-idₛ : ∀ {n} → extˢ (idₛ {n}) ~ idₛ
-- extˢ-idₛ zero    = refl
-- extˢ-idₛ (suc x) = refl

-- sub-idₛ : ∀ {n} (t : Ty n) → sub idₛ t ≡ t
-- sub-idₛ `𝟙         = refl
-- sub-idₛ (t₁ `× t₂) = cong₂ _`×_ (sub-idₛ t₁) (sub-idₛ t₂)
-- sub-idₛ (t₁ `+ t₂) = cong₂ _`+_ (sub-idₛ t₁) (sub-idₛ t₂)
-- sub-idₛ (` x)      = refl
-- sub-idₛ (ind t)    = cong ind (trans (sub~ {t = t} extˢ-idₛ)
--                                      (sub-idₛ t))

-- wk-cancels-,ₛ : ∀ {m n} (σ : Sub m n) T
--     → suc ᴿ⨟ˢ (σ ,ₛ T) ~ σ
-- wk-cancels-,ₛ σ T zero    = refl
-- wk-cancels-,ₛ σ T (suc x) = refl

-- comm-⨟-σ₀ : ∀ {n m} (σ : Sub m n) T
--   → (σ₀ T ˢ⨟ˢ σ) ~ (extˢ σ ˢ⨟ˢ σ₀ (sub σ T))
-- comm-⨟-σ₀ σ T zero = refl
-- comm-⨟-σ₀ σ T (suc x) =
--   begin
--     (σ₀ T ˢ⨟ˢ σ) (suc x)
--   ≡⟨⟩
--     σ x
--   ≡⟨ sym (sub-idₛ (σ x)) ⟩
--     sub idₛ (σ x)
--   ≡⟨ sym (sub~ {t = σ x} (wk-cancels-,ₛ idₛ (sub σ T))) ⟩
--     sub (suc ᴿ⨟ˢ (idₛ ,ₛ sub σ T)) (σ x)
--   ≡⟨ sym (ren-sub suc (idₛ ,ₛ sub σ T) (σ x)) ⟩
--     sub (idₛ ,ₛ sub σ T) (ren suc (σ x))
--   ≡⟨⟩
--     (extˢ σ ˢ⨟ˢ σ₀ (sub σ T)) (suc x)
--   ∎

-- {-# TERMINATING #-}
-- \end{code}
-- \newcommand\ccFunFmap{%
-- \begin{code}
-- fmap : ∀ {T} {G₀ : Ty 1}
--   → (f : ⟦ ind G₀ ⟧ᵀ → ⟦ T ⟧ᵀ) (G : Ty 1)
--   → ⟦ sub₀ (ind G₀) G ⟧ᵀ → ⟦ sub₀ T G ⟧ᵀ
-- fmap f `𝟙 tt = tt
-- fmap f (G `× H) (x , y) = fmap f G x , fmap f H y
-- fmap f (G `+ H) (inj₁ x) = inj₁ (fmap f G x)
-- fmap f (G `+ H) (inj₂ y) = inj₂ (fmap f H y)
-- fmap f (` zero) v = f v
-- \end{code}
-- }
-- \begin{code}[hide]
-- fmap {T = T} {G₀ = G₀} f (ind G) (fold x) =
--   fold (subst ⟦_⟧ᵀ (eq (σ₀ T))
--         (fmap{T}{G₀} f G′
--          (subst ⟦_⟧ᵀ (sym (eq (σ₀ (ind G₀)))) x)))
--   where
--     G′ : Ty 1
--     G′ = sub (σ₀ (ind G)) G
--     eq : ∀ (τ : Sub 1 0) → sub τ G′ ≡ sub₀ (ind (sub (extˢ τ) G)) (sub (extˢ τ) G)
--     eq τ = begin
--        sub τ G′
--      ≡⟨ sub-sub (σ₀ (ind G)) τ G ⟩
--        sub (σ₀ (ind G) ˢ⨟ˢ τ) G
--      ≡⟨ sub~ {t = G} (comm-⨟-σ₀ τ (ind G)) ⟩
--        sub (extˢ τ ˢ⨟ˢ σ₀ (sub τ (ind G))) G
--      ≡⟨ sym (sub-sub (extˢ τ) (σ₀ (sub τ (ind G))) G) ⟩
--        sub₀ (ind (sub (extˢ τ) G)) (sub (extˢ τ) G)
--      ∎
-- --- needs to be recursive over `ind G`

-- {-# TERMINATING #-}
-- \end{code}
-- \newcommand\ccFunEval{%
-- \begin{code}
eval : ∀ {n : ℕ} {ctx : Ctx n} {ty} → Exp ctx ty →  HVec (λ x → ⟦ x ⟧ᵀ) ctx → ⟦ ty ⟧ᵀ
eval `0 ctx = tt
eval (App f x) ctx = eval f ctx (eval x ctx)
eval (Var f) ctx = hlookup ctx f
eval (Lam exp) ctx = λ x → eval exp (x ∷ᴴ ctx)
eval (`# expL expR) ctx = eval expL ctx , eval expR ctx
eval (π₁ exp) ctx = proj₁ (eval exp ctx)
eval (π₂ exp) ctx = proj₂ (eval exp ctx)
eval (ι₁ exp) ctx = inj₁ ((eval exp ctx))
eval (ι₂ exp) ctx = inj₂ ((eval exp ctx))
eval (`case exp l r) ctx with eval exp ctx 
... | inj₁ res = eval l (res ∷ᴴ ctx)
... | inj₂ res = eval r (res ∷ᴴ ctx)

embedd-Ty : ∀ {n} → PF.Ty n → Ty n
embedd-Ty PF.`𝟙 = `𝟙
embedd-Ty (tyA PF.`× tyB) = embedd-Ty tyA `× embedd-Ty tyB
embedd-Ty (tyA PF.`+ tyB) = embedd-Ty tyA `+ embedd-Ty tyB
embedd-Ty (PF.` x) = ` x
embedd-Ty (PF.ind ty) = ind (embedd-Ty ty)

weaken : ∀ {n : ℕ} {ctx : Ctx n} {tyA tyB } →  Exp ctx tyA → Exp (tyB ∷ ctx) tyA
weaken exp = {!   !}



embedd-Exp : ∀ {tyA tyB : PF.TY} →  tyA PF.→ᴾ tyB → Exp [] (embedd-Ty tyA ⇒ embedd-Ty tyB )
embedd-Exp PF.`0 = Lam `0
embedd-Exp PF.id = Lam (Var zero)
embedd-Exp (PF.C f g) = Lam (App (weaken (embedd-Exp f)) (App ((weaken (embedd-Exp g))) (Var zero)))
embedd-Exp (PF.`# l r) = Lam (`# (App (weaken (embedd-Exp l)) (Var zero)) ((App (weaken (embedd-Exp r)) (Var zero))))
embedd-Exp PF.π₁ = Lam (π₁ (Var zero))
embedd-Exp PF.π₂ = Lam (π₂ (Var zero))
embedd-Exp PF.ι₁ = Lam (ι₁ ((Var zero)))
embedd-Exp PF.ι₂ = Lam (ι₂ ((Var zero)))
embedd-Exp (PF.`case f g) = Lam (`case (Var zero) (App (weaken (weaken (embedd-Exp f))) (Var zero)) {!   !})
embedd-Exp PF.fold = {!   !}
embedd-Exp (PF.P exp) = {!   !}
embedd-Exp (PF.F exp) = {!   !}
-- \end{code}
-- }
-- \begin{code}[hide]
-- eval (F {G = G} h) = λ{ (fold x , u) → eval h ((fmap (λ v → eval (F h) (v , u)) G x) , u) }
-- \end{code}

-- \begin{code}[hide]
-- mkvec : Ty 0 → ℕ → Ty 0
-- mkvec T zero = `𝟙
-- mkvec T (suc n) = T `× mkvec T n

-- lookup : (i : Fin n) → mkvec T n →ᴾ T
-- lookup zero = π₁
-- lookup (suc i) = C (lookup i) π₂
-- \end{code}
-- \newcommand\ccFunAssocDist{%
-- \begin{code}
-- assoc-× : (U `× V) `× T →ᴾ U `× (V `× T)
-- assoc-× = `# (C π₁ π₁) (`# (C π₂ π₁) π₂)

-- postulate
--   dist-+-x : (U `+ V) `× T →ᴾ (U `× T) `+ (V `× T)
-- \end{code}
-- }
-- \begin{code}[hide]
-- module FromNats where
-- \end{code}
-- \newcommand\ccDefGNat{%
-- \begin{code}
--   G-Nat : Ty 1
--   G-Nat = `𝟙 `+ ` zero

--   Nat = ind G-Nat

--   _ : sub₀ Nat G-Nat ≡ (`𝟙 `+ Nat)
--   _ = refl

--   -- zero
--   _ : `𝟙 →ᴾ Nat
--   _ = C fold ι₁

--   _ : `𝟙 →ᴾ (`𝟙 `+ Nat)
--   _ = ι₁

--   -- successor
--   _ : Nat →ᴾ Nat
--   _ = C fold ι₂

--   _ : Nat →ᴾ (`𝟙 `+ Nat)
--   _ = ι₂
-- \end{code}
-- }
