

\begin{code}[hide]
{-# OPTIONS --rewriting #-}

{-# OPTIONS --allow-unsolved-metas #-}
module PR-CC-ind where


open import Data.Fin using (Fin; zero; suc)
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
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)
open import Utils
open import Agda.Builtin.Equality.Rewrite


infix 6 _→ᴾ_
infix 7 _`×_
infix 8 _`+_
\end{code}
\newcommand\ccDataTy{%
\begin{code}

data Ty n :  Set where
  `𝟙   : Ty n
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
mapˢᴿ f `𝟙 = `𝟙
mapˢᴿ f (tyA `× tyB) = mapˢᴿ f tyA `× mapˢᴿ f tyB
mapˢᴿ f (tyA `+ tyB) = (mapˢᴿ f tyA) `+ (mapˢᴿ f tyB)
mapˢᴿ f (` x) = “ (f x) ”
mapˢᴿ {n'}{m} f (ind ty) = ind (mapˢᴿ (ext {n = n'} f)  ty)


map-cong : ∀{n m}{T}{{_ : Mappable T}}{σ τ : T ⊢ n ⇒ m}
  → (∀(x : Fin n) → σ x ≡ τ x)
  → ∀(ty : Ty n)
  → mapˢᴿ σ ty ≡ mapˢᴿ τ ty
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

σ₀ : Ty 0 → Sub 1 0
σ₀ T zero = T

sub₀ : Ty 0 → Ty 1 → Ty 0
sub₀ T       = sub (σ₀ T)


record Composable (T₁ T₂ T₃ : ℕ → Set)
   {{_ : Mappable T₁}} {{_ : Mappable T₂}} {{_ : Mappable T₃}} : Set₁ where
   infixr 5 _⨟_
   field _⨟_ : ∀{n m o} → T₁ ⊢ n ⇒ m   → T₂ ⊢ m ⇒ o  →  T₃ ⊢ n ⇒ o
   
   field ext-⨟ : ∀{n m o} → (σ₁ : T₁ ⊢ n ⇒ m) →  (σ₂ : T₂ ⊢ m ⇒ o) → ∀(x : Fin (suc n)) → (ext σ₁ ⨟ ext σ₂) x ≡ ext (σ₁ ⨟ σ₂) x
   field map-“” : ∀{n m o} → (σ : T₁ ⊢ n ⇒ m) → (τ : T₂ ⊢ m ⇒ o) → ∀(x : Fin n) → mapˢᴿ τ “ σ x ” ≡ “ (σ ⨟ τ) x ”

open Composable {{...}} public

-- map-fusionˢ = {!   !}


map-fusion : ∀ {n m o}{T₁ T₂ T₃}
   {{_ : Mappable T₁}}{{_ : Mappable T₂}}{{_ : Mappable T₃}}
   {{_ : Composable T₁ T₂ T₃}}
   → (σ : T₁ ⊢ n ⇒ m) → (τ : T₂ ⊢ m ⇒ o) →  (ty : Ty n)
   → mapˢᴿ τ (mapˢᴿ σ ty) ≡ mapˢᴿ (σ ⨟ τ) ty
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



subsub123 : ∀ (T0 : Ty 0) (T1 : Ty 1) (T2 : Ty 2)
  →  sub₀ T0 (sub (λ{ zero → T1; (suc zero) → ` zero }) T2)
  ≡ sub (λ{ zero → sub₀ T0 T1; (suc zero) → T0}) T2
subsub123 T0 T1 T2 = {!   !} -- subsub{m = 1}{o = 0}{n = 2} (λ{ zero → T0}) (λ{ zero → T1 ; (suc zero) → ` zero}) {!T2!}



variable
  T U V : TY
  G : Ty 1
\end{code}
\newcommand\ccDataPR{%
\begin{code}
data _→ᴾ_ : TY → TY → Set where
  `0 : T →ᴾ `𝟙
  id : T →ᴾ T
  C  : (f : U →ᴾ V) → (g : T →ᴾ U) → (T →ᴾ V)
  --
  `# : (f : T →ᴾ U) → (g : T →ᴾ V) → (T →ᴾ U `× V)
  π₁ : U `× V →ᴾ U
  π₂ : U `× V →ᴾ V
  --
  ι₁ : U →ᴾ U `+ V
  ι₂ : V →ᴾ U `+ V
  `case : (f : U →ᴾ T) → (g : V →ᴾ T) → U `+ V →ᴾ T
  --
  fold : sub₀ (ind G) G →ᴾ ind G
  P : (h : sub₀ (T `× ind G) G `× U →ᴾ T) → (ind G `× U →ᴾ T)
\end{code}
}
\begin{code}[hide]
  F : (h : sub₀ T G `× (sub₀ (ind G) G `× U) →ᴾ T)
    → (ind G `× U →ᴾ T)
-- or more generally with n-ary sum and product types
  -- π : {T* : Vec (Ty 0) n} → (i : Fin n) → `X T* →ᴾ lookup T* i
  -- ι : {T* : Vec (Ty 0) n} → (i : Fin n) → lookup T* i → `suc T*
-- interpretation
\end{code}
\newcommand\ccDataAlg{%
\begin{code}
⟦_⟧ᵀ : TY → Set

data Alg (G : Ty 1) : Set where
  fold : ⟦ sub₀ (ind G) G ⟧ᵀ → Alg G 

⟦ `𝟙 ⟧ᵀ     = ⊤
⟦ T `× U ⟧ᵀ = ⟦ T ⟧ᵀ × ⟦ U ⟧ᵀ
⟦ T `+ U ⟧ᵀ = ⟦ T ⟧ᵀ ⊎ ⟦ U ⟧ᵀ
⟦ ind G ⟧ᵀ  = Alg G
\end{code}
}
\begin{code}[hide]
fmap : ∀ {T} {G₀ : Ty 1}
  → (f : ⟦ ind G₀ ⟧ᵀ → ⟦ T ⟧ᵀ) (G : Ty 1)
  → ⟦ sub₀ (ind G₀) G ⟧ᵀ → ⟦ sub₀ T G ⟧ᵀ
fmap f `𝟙 tt = tt
fmap f (G `× H) (x , y) = (fmap f G x) , (fmap f H y)
fmap f (G `+ H) (inj₁ x) = inj₁ (fmap f G x)
fmap f (G `+ H) (inj₂ y) = inj₂ (fmap f H y)
fmap f (` zero) v = f v
fmap f (ind G) (fold x) = fold {!!}
--- needs to be recursive over `ind G`
\end{code}
\newcommand\ccFunFmap{%
\begin{code}
fmap′ : ∀ {T}{G₀ : Ty 1} (G : Ty 1) (f : ⟦ ind G₀ ⟧ᵀ → ⟦ T ⟧ᵀ)
  → ⟦ sub₀ (ind G₀) G ⟧ᵀ → ⟦ sub₀ (T `× ind G₀) G ⟧ᵀ
fmap′ `𝟙       f tt        = tt
fmap′ (G `× H) f (x , y)   = (fmap′ G f x) , (fmap′ H f y)
fmap′ (G `+ H) f (inj₁ x) = inj₁ (fmap′ G f x)
fmap′ (G `+ H) f (inj₂ y) = inj₂ (fmap′ H f y)
fmap′ (` zero) f v         = f v , v
\end{code}
}
\begin{code}[hide]
fmap′ {_}{G₀} (ind G) f (fold x) =
  let G′ : Ty 1
      G′ = sub σ₁ G
      eq : sub₀ (ind G₀) (sub σ₁ G)
         ≡ sub₀ (ind (sub (extˢ (σ₀ (ind G₀))) G)) (sub (extˢ (σ₀ (ind G₀))) G)
      eq = begin
             sub₀ (ind G₀) (sub σ₁ G)
           ≡⟨⟩
             sub (σ₀ (ind G₀)) (sub σ₁ G)
           ≡⟨ map-fusion σ₁ (σ₀ (ind G₀)) G ⟩
             {!!}
           ≡⟨ {!!} ⟩
             {!!}
           ≡˘⟨ sub-sub (extˢ (σ₀ (ind G₀))) (σ₀ (ind (sub (extˢ (σ₀ (ind G₀))) G))) G ⟩
             sub (σ₀ (ind (sub (extˢ (σ₀ (ind G₀))) G))) (sub (extˢ (σ₀ (ind G₀))) G) ∎
      r′ = fmap′ G′ f (subst ⟦_⟧ᵀ (sym eq) x)
  in fold {!!}
  where
    σ₁ : Sub 2 1
    σ₁ zero = ind G
    σ₁ (suc i) = ` zero
    
--- needs to be recursive over `ind G`

{-# TERMINATING #-}
\end{code}
\newcommand\ccFunEval{%
\begin{code}
eval : (T →ᴾ U) → ⟦ T ⟧ᵀ → ⟦ U ⟧ᵀ
eval `0       = const tt
eval id       = λ v → v
eval (C f g)  = eval f ∘ eval g
eval (`# f g) = ⟨ eval f , eval g ⟩
eval π₁       = proj₁
eval π₂       = proj₂
eval ι₁       = inj₁
eval ι₂       = inj₂
eval (`case f g) = λ{ (inj₁ x) → eval f x ; (inj₂ y) → eval g y}
eval fold     = fold
eval (P {G = G} h) = λ{ (fold x , u) → eval h ((fmap′ G (λ v → eval (P h) (v , u)) x) , u)}
\end{code}
}
\begin{code}[hide]
eval (F {G = G} p) = λ{ (fold x , u) → eval p ((fmap (λ v → eval (F p) (v , u)) G x) , (x , u))}
\end{code}

\begin{code}[hide]
mkvec : Ty 0 → ℕ → Ty 0
mkvec T zero = `𝟙
mkvec T (suc n) = T `× mkvec T n

lookup : (i : Fin n) → mkvec T n →ᴾ T
lookup zero = π₁
lookup (suc i) = C (lookup i) π₂
\end{code}
\newcommand\ccFunAssocDist{%
\begin{code}
assoc-× : (U `× V) `× T →ᴾ U `× (V `× T)
assoc-× = `# (C π₁ π₁) (`# (C π₂ π₁) π₂)

postulate
  dist-+-x : (U `+ V) `× T →ᴾ (U `× T) `+ (V `× T)
\end{code}
}
\begin{code}[hide]
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

  import PR-Nat as Nats

\end{code}
\newcommand\ccDefNatToInd{%
\begin{code}
  ⟦_⟧  : Nats.PR n → mkvec Nat n →ᴾ Nat
  ⟦_⟧* : Vec (Nats.PR n) m → mkvec Nat n →ᴾ mkvec Nat m

  ⟦ Nats.Z ⟧      = C fold ι₁
  ⟦ Nats.σ ⟧      = C (C fold ι₂) π₁
  ⟦ Nats.π i ⟧    = lookup i
  ⟦ Nats.C f g* ⟧ = C ⟦ f ⟧ ⟦ g* ⟧*
  ⟦ Nats.P g h ⟧  = P (C (`case (C ⟦ g ⟧ π₂) (C ⟦ h ⟧ assoc-×)) dist-+-x)

  ⟦ [] ⟧*         = `0
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

  ⟦_⟧ᴬ : ⟦ Alpha ⟧ᵀ → `𝟙 →ᴾ Alpha
  ⟦ inj₁ tt ⟧ᴬ = ι₁
  ⟦ inj₂ tt ⟧ᴬ = ι₂

  import PR-Words as Words

  ⟦_⟧  : Words.PR ⟦ Alpha ⟧ᵀ n → mkvec Alpha* n →ᴾ Alpha*
  ⟦_⟧* : Vec (Words.PR ⟦ Alpha ⟧ᵀ n) m → mkvec Alpha* n →ᴾ mkvec Alpha* m

  ⟦ Words.Z ⟧ = C (C fold ι₁) `0
  ⟦ Words.σ a ⟧ = C (C fold (C ι₂ (`# (C ⟦ a ⟧ᴬ `0) id))) π₁
  ⟦ Words.π i ⟧ = lookup i
  ⟦ Words.C f g* ⟧ = C ⟦ f ⟧ ⟦ g* ⟧*
  ⟦ Words.P g h ⟧ = P (C (`case (C ⟦ g ⟧ π₂) (C (C (C (`case (C ⟦ h (inj₁ tt) ⟧ assoc-×) (C ⟦ h (inj₂ tt) ⟧ assoc-×)) dist-+-x) (`# (C (`case (C ι₁ π₂) (C ι₂ π₂)) π₁) π₂)) (`# (C dist-+-x π₁) π₂))) dist-+-x)

  ⟦ [] ⟧*         = `0
  ⟦ p ∷ p* ⟧*     = `# ⟦ p ⟧ ⟦ p* ⟧*

module FromTrees where
  -- generic stuff
  symbols : (G : Ty 1) → Set
  symbols G = ⟦ sub₀ `𝟙 G ⟧ᵀ

  -- enumerate symbols
  dom : (G : Ty 1) → List (symbols G)
  dom `𝟙 =  tt ∷ []
  dom (G `× H) = concat (map (λ g → map (λ h → g , h) (dom H)) (dom G))
  dom (G `+ H) = map inj₁ (dom G) ++ map inj₂ (dom H)
  dom (` zero) = tt ∷ []
  dom (ind G) = {!!}

  rank : (G : Ty 1) → symbols G → ℕ
  rank `𝟙 tt = 0
  rank (G `× H) (g , h) = rank G g + rank H h
  rank (G `+ H) (inj₁ g) = rank G g
  rank (G `+ H) (inj₂ h) = rank H h
  rank (` zero) tt = 1
  rank (ind G) sym-G = {!!}

  import PR-Trees as Trees

  -- binary trees with signature { Leaf:0, Branch:2 }
  G-Btree : Ty 1
  G-Btree = `𝟙 `+ (` zero `× ` zero)

  Btree : Ty 0
  Btree = ind G-Btree

  R-Btree : Trees.Ranked
  R-Btree = Trees.mkRanked (rank G-Btree)

  ⟦_⟧  : Trees.PR R-Btree n → mkvec Btree n →ᴾ Btree
  ⟦_⟧* : Vec (Trees.PR R-Btree n) m → mkvec Btree n →ᴾ mkvec Btree m

  ⟦ Trees.σ (inj₁ tt) ⟧ = C fold ι₁
  ⟦ Trees.σ (inj₂ (tt , tt)) ⟧ = C fold (C ι₂ (`# π₁ (C π₁ π₂)))
  ⟦ Trees.π i ⟧ = lookup i
  ⟦ Trees.C f g* ⟧ = C ⟦ f ⟧ ⟦ g* ⟧*
  ⟦ Trees.P h ⟧ = P (C (`case (C ⟦ h (inj₁ tt) ⟧ π₂)
                              (C ⟦ h (inj₂ (tt , tt)) ⟧ (`# (C π₁ (C π₁ π₁)) (`# (C π₂ (C π₁ π₁)) (`# (C π₁ (C π₂ π₁)) (`# (C π₂ (C π₂ π₁)) π₂))))))
                       dist-+-x)
  
  ⟦ [] ⟧*         = `0
  ⟦ p ∷ p* ⟧*     = `# ⟦ p ⟧ ⟦ p* ⟧*
\end{code}
