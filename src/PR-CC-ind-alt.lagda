
\begin{code}[hide]
{-# OPTIONS --rewriting  #-}

module PR-CC-ind-alt where


open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; [] ; _∷_; _++_; map; concat)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Vec using (Vec;[];_∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂) renaming (<_,_> to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; const) renaming (id to identity)
open import Data.Product using (Σ)
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

data PolyTyOp  :  Set where
  `𝟙   : PolyTyOp
  _`×_ : PolyTyOp → PolyTyOp → PolyTyOp
  _`+_ : PolyTyOp → PolyTyOp → PolyTyOp
  `t   : PolyTyOp
  

data Ty :    Set where
  `𝟙   :  Ty 
  _`×_ :  Ty  → Ty   → Ty 
  _`+_ : Ty  → Ty  → Ty 
  ind  : PolyTyOp → Ty
  _⇒_ : Ty → Ty → Ty


-- https://stackoverflow.com/questions/43083123/how-to-define-a-functor-fixpoint
⟦_⟧ₚ : PolyTyOp → Set → Set
⟦ `𝟙 ⟧ₚ arg = ⊤
⟦ ptoA `× ptoB ⟧ₚ arg = ⟦ ptoA ⟧ₚ arg × ⟦ ptoB ⟧ₚ arg
⟦ ptoA `+ ptoB ⟧ₚ arg = ⟦ ptoA ⟧ₚ arg ⊎ ⟦ ptoB ⟧ₚ arg
⟦ `t ⟧ₚ arg = arg

data Fix (F : PolyTyOp) : Set where
    fold : ⟦ F ⟧ₚ (Fix F) → Fix F 


-- tyToTyOp : Ty → PolyTyOp
-- tyToTyOp `𝟙 = `𝟙
-- tyToTyOp (tyA `× tyB) = tyToTyOp tyA `× tyToTyOp tyB
-- tyToTyOp (tyA `+ tyB) = tyToTyOp tyA `+ tyToTyOp tyB
-- tyToTyOp (ind x) = {!   !} -- not possible
-- tyToTyOp (ty ⇒ ty₁) = {!   !} -- not possible

TY = Ty

sub₀ : Ty → PolyTyOp → Ty
sub₀ ty `𝟙 = `𝟙
sub₀ ty (pt1 `× pt2) = (sub₀ ty pt1) `× (sub₀ ty pt2)
sub₀ ty (pt1 `+ pt2) = (sub₀ ty pt1) `+ (sub₀ ty pt2)
sub₀ ty `t = ty

\end{code}
}



\begin{code}
variable
  T U V : TY
  G : PolyTyOp
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
  P :  ∀ {T U} {G}  (h : sub₀ (T `× ind G) G `× U →ᴾ T) → (ind G `× U →ᴾ T)
\end{code}
}

\begin{code}[hide]
  F : ∀ {T U} {G}  (h : sub₀ T G `× U →ᴾ T) → (ind G `× U →ᴾ T)

-- interpretation
\end{code}

\newcommand\ccDataAlg{%
\begin{code}
⟦_⟧ᵀ : TY → Set

-- data Alg (G : PolyTyOp) : Set where
--   fold : ⟦ sub₀ (ind G) G ⟧ᵀ → Alg G 

⟦ `𝟙 ⟧ᵀ     = ⊤
⟦ T `× U ⟧ᵀ = ⟦ T ⟧ᵀ × ⟦ U ⟧ᵀ
⟦ T `+ U ⟧ᵀ = ⟦ T ⟧ᵀ ⊎ ⟦ U ⟧ᵀ
⟦ ind G ⟧ᵀ  = Fix G
⟦ tyA ⇒ tyB ⟧ᵀ = ⟦ tyA ⟧ᵀ → ⟦ tyB ⟧ᵀ
\end{code}
}

\begin{code}[hide]
helper : ∀ (G : PolyTyOp) (ty : Ty) → ⟦ G ⟧ₚ ⟦ ty ⟧ᵀ ≡ (λ y → ⟦ sub₀ y G ⟧ᵀ ) ty
helper `𝟙 ty = refl
helper (G1 `× G2) ty = cong₂ _×_ (helper G1 ty) (helper G2 ty)
helper (G1 `+ G2) ty = cong₂ _⊎_ (helper G1 ty) (helper G2 ty)
helper `t ty = refl

helper2 : ∀ (G : PolyTyOp) → ⟦ G ⟧ₚ (Fix G) ≡ ⟦ sub₀ (ind G) G ⟧ᵀ
helper2 G = helper G (ind G)

{-# REWRITE   helper2  #-}

\end{code}

\begin{code}[hide]
-- https://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf
mapFold : forall {X} F G -> (⟦ G ⟧ₚ X -> X) -> ⟦ F ⟧ₚ (Fix G) -> ⟦ F ⟧ₚ X
mapFold `𝟙 G φ x = tt
mapFold (F1 `× F2) G φ (x , y) = (mapFold F1 G φ x) , mapFold F2 G φ y
mapFold (F1 `+ F2) G φ (inj₁ x) = inj₁ (mapFold F1 G φ x)
mapFold (F1 `+ F2) G φ (inj₂ y) = inj₂ ((mapFold F2 G φ y))
mapFold `t G φ (fold x) = φ (mapFold G G φ x) 


foldF : {F : PolyTyOp}{A : Set} -> (⟦ F ⟧ₚ A -> A) -> Fix F -> A
foldF {pto} φ (fold x) = φ (mapFold pto pto φ x) 
\end{code}


\newcommand\ccFunFmap{%
\begin{code}
fmap : ∀ {S}{T}
  → (f : ⟦ S ⟧ᵀ → ⟦ T ⟧ᵀ) (G : PolyTyOp)
  → ⟦ sub₀ S G ⟧ᵀ → ⟦ sub₀ T G ⟧ᵀ
fmap f `𝟙 tt = tt
fmap f (pto1 `× pto2) (x , y) = fmap f pto1 x , fmap f pto2 y
fmap f (pto1 `+ pto2) (inj₁ x) = inj₁ (fmap f pto1 x)
fmap f (pto1 `+ pto2) (inj₂ y) = inj₂ (fmap f pto2 y)
fmap f `t x = f x 
\end{code}
}



-- {-# TERMINATING #-}
\end{code}
\newcommand\ccFunEval{%
\begin{code}
{-# REWRITE   helper  #-}

-- {-# TERMINATING #-}
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
eval fold  =  fold
eval (P {G = G} h) =   λ {(x , u) → foldF (λ gu → eval h (fmap (λ u' → u' , x) G gu , u)) x} --   λ{ (fold x , u) → eval h ((fmap (λ v → (eval (P h) (v , u)) , v) G x) , u)}
\end{code}
}
\begin{code}[hide]
eval (F {G = G} h) =  λ{ (x , u) → foldF (λ gu → eval h (gu , u)) x } --  λ{ (fold x , u) → eval h ((fmap (λ v → eval (F h) (v , u)) G x) , u) }
\end{code}

\begin{code}[hide]
mkvec : Ty → ℕ → Ty
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
  G-Nat : PolyTyOp
  G-Nat = `𝟙 `+ `t

  Nat = ind G-Nat

  _ : sub₀ Nat G-Nat ≡ (`𝟙 `+ Nat)
  _ = refl

  -- zero
  _ : `𝟙 →ᴾ Nat
  _ = C fold ι₁

  _ : `𝟙 →ᴾ (`𝟙 `+ Nat)
  _ = ι₁

  -- successor
  _ : Nat →ᴾ Nat
  _ = C fold ι₂

  _ : Nat →ᴾ (`𝟙 `+ Nat)
  _ = ι₂
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
  Alpha : Ty
  Alpha = `𝟙 `+ `𝟙

  G-Alpha* : PolyTyOp
  G-Alpha* = `𝟙 `+ ((`𝟙 `+ `𝟙) `×  `t)

  Alpha* : Ty
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
  symbols : (G : PolyTyOp) → Set
  symbols G = ⟦ sub₀ `𝟙 G ⟧ᵀ

  dom : ∀ (G : PolyTyOp)  → List (symbols G)
  dom `𝟙 = tt ∷ []
  dom (pg `× ph) = concat (map (λ g → map (λ h → g , h) (dom ph)) (dom pg))
  dom (pg `+ ph) = map inj₁ (dom pg) ++ map inj₂ (dom ph)
  dom `t = tt ∷ []


  rank : ∀ (G : PolyTyOp) → symbols G → ℕ
  rank `𝟙 tt = 0
  rank (pg `× ph) (gs , hs) = rank pg gs + rank ph hs
  rank (pg `+ ph) (inj₁ gs) = rank pg gs
  rank (pg `+ ph) (inj₂ hs) = rank ph hs
  rank `t tt = 1

  import PR-Trees as Trees

  -- binary trees with signature { Leaf:0, Branch:2 }
  G-Btree : PolyTyOp
  G-Btree = `𝟙 `+ (`t `× `t)

  Btree : Ty
  Btree = ind G-Btree

  G-Btree-polynomial : PolyTyOp
  G-Btree-polynomial =  `𝟙 `+ (`t  `× `t)

  R-Btree : Trees.Ranked
  R-Btree = Trees.mkRanked (rank G-Btree-polynomial)

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
