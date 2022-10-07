\begin{code}[hide]
{-# OPTIONS --allow-unsolved-metas #-}
module PR-CC-ind where

open import Data.Fin using (Fin; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; [] ; _∷_; _++_; map; concat)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Vec using (Vec;[];_∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂) renaming (<_,_> to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; const)
import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)
open import Utils


infix 6 _→ᴾ_
infix 7 _`×_
infix 8 _`+_
\end{code}
\newcommand\ccDataTy{%
\begin{code}
data Ty n : Set where
  `𝟙   : Ty n
  _`×_ : Ty n → Ty n → Ty n
  _`+_ : Ty n → Ty n → Ty n
  `    : Fin n → Ty n
  ind  : Ty (suc n) → Ty n

TY = Ty 0
\end{code}
}
\begin{code}[hide]
Ren : ℕ → ℕ → Set
Ren n m = Fin n → Fin m

extᴿ : Ren n m → Ren (suc n) (suc m)
extᴿ ρ zero    = zero
extᴿ ρ (suc x) = suc (ρ x)

ren : Ren n m → Ty n → Ty m
ren ρ `𝟙       = `𝟙
ren ρ (T `× U) = ren ρ T `× ren ρ U
ren ρ (T `+ U) = ren ρ T `+ ren ρ U
ren ρ (` x)    = ` (ρ x)
ren ρ (ind G)  = ind (ren (extᴿ ρ) G)

Sub : ℕ → ℕ → Set
Sub n m = Fin n → Ty m

extˢ : Sub n m → Sub (suc n) (suc m)
extˢ σ zero    = ` zero
extˢ σ (suc x) = ren suc (σ x)

sub : Sub n m → Ty n → Ty m
sub σ `𝟙       = `𝟙
sub σ (T `× U) = sub σ T `× sub σ U
sub σ (T `+ U) = sub σ T `+ sub σ U
sub σ (` x)    = σ x
sub σ (ind G)  = ind (sub (extˢ σ) G)

sub₀ : Ty 0 → Ty 1 → Ty 0
sub₀ T G       = sub (λ{ zero → T}) G

subext : (σ₁ : Sub m o) (σ₂ : Sub n m) → ∀ x → (sub (extˢ σ₁) ∘ extˢ σ₂) x ≡ extˢ (sub σ₁ ∘ σ₂) x
subext σ₁ σ₂ zero = refl
subext σ₁ σ₂ (suc x) = begin
                        (sub (extˢ σ₁) ∘ extˢ σ₂) (suc x)
                      ≡⟨⟩
                        sub (extˢ σ₁) (extˢ σ₂ (suc x))
                      ≡⟨⟩
                        sub (extˢ σ₁) (ren suc (σ₂ x))
                      ≡⟨ {!!} ⟩
                        {!!}

subsub : (σ₁ : Sub m o) (σ₂ : Sub n m) (T : Ty n) → sub σ₁ (sub σ₂ T) ≡ sub (sub σ₁ ∘ σ₂) T
subsub σ₁ σ₂ `𝟙 = refl
subsub σ₁ σ₂ (T `× U) rewrite subsub σ₁ σ₂ T | subsub σ₁ σ₂ U = refl
subsub σ₁ σ₂ (T `+ U) rewrite subsub σ₁ σ₂ T | subsub σ₁ σ₂ U = refl
subsub σ₁ σ₂ (` x) = refl
subsub σ₁ σ₂ (ind T) rewrite subsub (extˢ σ₁) (extˢ σ₂) T = cong ind (cong (λ σ → sub σ T) {!subext σ₁ σ₂!})


subsub123 : ∀ (T0 : Ty 0) (T1 : Ty 1) (T2 : Ty 2)
  →  sub₀ T0 (sub (λ{ zero → T1; (suc zero) → ` zero }) T2)
  ≡ sub (λ{ zero → sub₀ T0 T1; (suc zero) → T0}) T2
subsub123 T0 T1 T2 = subsub{m = 1}{o = 0}{n = 2} (λ{ zero → T0}) (λ{ zero → T1 ; (suc zero) → ` zero}) {!T2!}



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
  -- ι : {T* : Vec (Ty 0) n} → (i : Fin n) → lookup T* i → `S T*
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
      G′ = sub (λ{ zero → ind G ; (suc zero) → ` zero}) G
      r′ = fmap′ G′ f {!x!}
  in fold {!!}
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
