{-# OPTIONS --safe #-}

module Core.Semantics.Inductive where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Core.Semantics.Containers

----------------------------------------------------------------------
-- A W-style fixed point for nested inductive type codes
----------------------------------------------------------------------

data MuShape {n} (D : Container (suc n)) : Set where
  node : (s : Shape D) →
         (Position D s zero → MuShape D) →
         MuShape D

rootShape : ∀ {n} {D : Container (suc n)} → MuShape D → Shape D
rootShape (node s children) = s

branch : ∀ {n} {D : Container (suc n)} (tree : MuShape D) →
         Position D (rootShape tree) zero → MuShape D
branch (node s children) = children

data MuPos {n} (D : Container (suc n)) : MuShape D → Fin n → Set where
  here : ∀ {s children i} →
         Position D s (suc i) →
         MuPos D (node s children) i
  below : ∀ {s children i} →
          (p : Position D s zero) →
          MuPos D (children p) i →
          MuPos D (node s children) i

muC : ∀ {n} → Container (suc n) → Container n
muC D = record
  { Shape    = MuShape D
  ; Position = MuPos D
  }

extend : ∀ {n} → Set → (Fin n → Set) → Fin (suc n) → Set
extend X ρ zero    = X
extend X ρ (suc i) = ρ i

Mu : ∀ {n} → Container (suc n) → (Fin n → Set) → Set
Mu D ρ = Value (muC D) ρ

-- The constructor and destructor are definable without any positivity or
-- termination pragma.  The fixed point is carried entirely by MuShape.
conC : ∀ {n} {D : Container (suc n)} {ρ : Fin n → Set} →
        Value D (extend (Mu D ρ) ρ) → Mu D ρ
conC (s , values) =
  node s (λ p → proj₁ (values zero p)) ,
  λ
    { i (here p)    → values (suc i) p
    ; i (below p q) → proj₂ (values zero p) i q
    }

outC : ∀ {n} {D : Container (suc n)} {ρ : Fin n → Set} →
          Mu D ρ → Value D (extend (Mu D ρ) ρ)
outC (node s children , holes) =
  s , λ
    { zero    p → children p , λ i q → holes i (below p q)
    ; (suc i) p → holes i (here p)
    }

-- Without assuming function extensionality, the other inverse is stated by
-- its four observable projections.
out-con-shape : ∀ {n} {D : Container (suc n)} {ρ : Fin n → Set}
                    (x : Value D (extend (Mu D ρ) ρ)) →
                    proj₁ (outC (conC x)) ≡ proj₁ x
out-con-shape (s , values) = refl

out-con-parameter : ∀ {n} {D : Container (suc n)} {ρ : Fin n → Set}
                        (x : Value D (extend (Mu D ρ) ρ))
                        (i : Fin n)
                        (p : Position D (proj₁ x) (suc i)) →
                        proj₂ (outC (conC x)) (suc i) p ≡ proj₂ x (suc i) p
out-con-parameter (s , values) i p = refl

out-con-child-shape : ∀ {n} {D : Container (suc n)} {ρ : Fin n → Set}
                          (x : Value D (extend (Mu D ρ) ρ))
                          (p : Position D (proj₁ x) zero) →
                          proj₁ (proj₂ (outC (conC x)) zero p) ≡
                          proj₁ (proj₂ x zero p)
out-con-child-shape (s , values) p = refl

out-con-child-value : ∀ {n} {D : Container (suc n)} {ρ : Fin n → Set}
                          (x : Value D (extend (Mu D ρ) ρ))
                          (p : Position D (proj₁ x) zero)
                          (i : Fin n)
                          (q : MuPos D (proj₁ (proj₂ x zero p)) i) →
                          proj₂ (proj₂ (outC (conC x)) zero p) i q ≡
                          proj₂ (proj₂ x zero p) i q
out-con-child-value (s , values) p i q = refl

con-out-root : ∀ {n} {D : Container (suc n)} {ρ : Fin n → Set}
                   {s : Shape D}
                   (children : Position D s zero → MuShape D)
                   (holes : ∀ i → MuPos D (node s children) i → ρ i) →
                   rootShape (proj₁ (conC (outC (node s children , holes)))) ≡ s
con-out-root children holes = refl

con-out-branch : ∀ {n} {D : Container (suc n)} {ρ : Fin n → Set}
                     {s : Shape D}
                     (children : Position D s zero → MuShape D)
                     (holes : ∀ i → MuPos D (node s children) i → ρ i)
                     (p : Position D s zero) →
                     branch (proj₁ (conC (outC (node s children , holes)))) p ≡ children p
con-out-branch children holes p = refl

con-out-here : ∀ {n} {D : Container (suc n)} {ρ : Fin n → Set}
                   {s : Shape D}
                   (children : Position D s zero → MuShape D)
                   (holes : ∀ i → MuPos D (node s children) i → ρ i)
                   (i : Fin n) (p : Position D s (suc i)) →
                   proj₂ (conC (outC (node s children , holes))) i (here p) ≡ holes i (here p)
con-out-here children holes i p = refl

con-out-below : ∀ {n} {D : Container (suc n)} {ρ : Fin n → Set}
                    {s : Shape D}
                    (children : Position D s zero → MuShape D)
                    (holes : ∀ i → MuPos D (node s children) i → ρ i)
                    (i : Fin n) (p : Position D s zero)
                    (q : MuPos D (children p) i) →
                    proj₂ (conC (outC (node s children , holes))) i (below p q) ≡
                    holes i (below p q)
con-out-below children holes i p q = refl

-- Structural paramorphism.  At every recursive position the algebra sees
-- both the recursive result and the original subtree.
paraLayerWith : ∀ {n} {D : Container (suc n)} {ρ : Fin n → Set} {A : Set}
                {s : Shape D}
                (children : Position D s zero → MuShape D)
                (holes : ∀ i → MuPos D (node s children) i → ρ i)
                (results : (p : Position D s zero) → A) →
                Value D (extend (A × Mu D ρ) ρ)
paraLayerWith {n} {D} {ρ} {A} {s} children holes results = s , layer
  where
  layer : ∀ i → Position D s i → extend (A × Mu D ρ) ρ i
  layer zero p = results p , (children p , child-holes)
    where
    child-holes : ∀ i → MuPos D (children p) i → ρ i
    child-holes i q = holes i (below p q)
  layer (suc i) p = holes i (here p)

paraGo : ∀ {n} {D : Container (suc n)} {ρ : Fin n → Set} {A : Set} →
         (Value D (extend (A × Mu D ρ) ρ) → A) →
         (tree : MuShape D) →
         (∀ i → MuPos D tree i → ρ i) → A
paraGo {n} {D} {ρ} {A} algebra (node s children) holes =
  algebra (paraLayerWith children holes results)
  where
  results : (p : Position D s zero) → A
  results p = paraGo algebra (children p) child-holes
    where
    child-holes : ∀ i → MuPos D (children p) i → ρ i
    child-holes i q = holes i (below p q)

paraC : ∀ {n} {D : Container (suc n)} {ρ : Fin n → Set} {A : Set} →
        (Value D (extend (A × Mu D ρ) ρ) → A) →
        Mu D ρ → A
paraC algebra (tree , holes) = paraGo algebra tree holes

-- The one-step view used by the paramorphism equation.
paraLayerC : ∀ {n} {D : Container (suc n)} {ρ : Fin n → Set} {A : Set} →
             (Value D (extend (A × Mu D ρ) ρ) → A) →
             Mu D ρ → Value D (extend (A × Mu D ρ) ρ)
paraLayerC {n} {D} {ρ} {A} algebra (node s children , holes) =
  paraLayerWith children holes results
  where
  results : (p : Position D s zero) → A
  results p = paraGo algebra (children p) child-holes
    where
    child-holes : ∀ i → MuPos D (children p) i → ρ i
    child-holes i q = holes i (below p q)

paraC-β : ∀ {n} {D : Container (suc n)} {ρ : Fin n → Set} {A : Set}
          (algebra : Value D (extend (A × Mu D ρ) ρ) → A)
          (x : Mu D ρ) →
          paraC algebra x ≡ algebra (paraLayerC algebra x)
paraC-β algebra (node s children , holes) = refl
