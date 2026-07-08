module Core.Models.PRHOSetoidContainer where

-- This module is deliberately not marked --safe.  The setoid/container
-- semantics below is explicit, including a W-type fixed point for positive
-- higher-order type codes.  The remaining trusted boundary is function
-- extensionality for exponential and W-branching shapes, the termination
-- argument for the substitution bridge, and the law package.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
import Data.Nat as Nat
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Level
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
import Relation.Binary.PropositionalEquality as Eq

open import Core.Types hiding (A; B; D; E; T; U; V; G; H)
import Core.Semantics.Containers as Cont
import Core.Models.PRHO as PRHO

private
  variable
    A B D E T U V : TY HO
    G H : Ty HO 1

----------------------------------------------------------------------
-- Small setoid and extensional-map layer
----------------------------------------------------------------------

record Setoid₀ : Set₁ where
  infix 4 _≈_
  field
    Carrier : Set
    _≈_ : Carrier → Carrier → Set
    reflˢ : ∀ {x} → x ≈ x
    symˢ : ∀ {x y} → x ≈ y → y ≈ x
    transˢ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

open Setoid₀

record _⟶_ (A B : Setoid₀) : Set where
  field
    to : Carrier A → Carrier B
    resp : ∀ {x y} → _≈_ A x y → _≈_ B (to x) (to y)

open _⟶_

infixr 9 _∘⇒_
infix 4 _≈⇒_

_≈⇒_ : ∀ {A B : Setoid₀} → A ⟶ B → A ⟶ B → Set
_≈⇒_ {A} {B} f g = (x : Carrier A) → _≈_ B (to f x) (to g x)

id⇒ : ∀ {A} → A ⟶ A
id⇒ = record
  { to = λ x → x
  ; resp = λ p → p
  }

_∘⇒_ : ∀ {A B C} → B ⟶ C → A ⟶ B → A ⟶ C
f ∘⇒ g = record
  { to = λ x → to f (to g x)
  ; resp = λ p → resp f (resp g p)
  }

⊥S : Setoid₀
⊥S = record
  { Carrier = ⊥
  ; _≈_ = λ ()
  ; reflˢ = λ {}
  ; symˢ = λ {}
  ; transˢ = λ {}
  }

⊤S : Setoid₀
⊤S = record
  { Carrier = ⊤
  ; _≈_ = λ _ _ → ⊤
  ; reflˢ = tt
  ; symˢ = λ _ → tt
  ; transˢ = λ _ _ → tt
  }

_×S_ : Setoid₀ → Setoid₀ → Setoid₀
A ×S B = record
  { Carrier = Carrier A × Carrier B
  ; _≈_ = λ x y → _≈_ A (proj₁ x) (proj₁ y) × _≈_ B (proj₂ x) (proj₂ y)
  ; reflˢ = reflˢ A , reflˢ B
  ; symˢ = λ p → symˢ A (proj₁ p) , symˢ B (proj₂ p)
  ; transˢ = λ p q → transˢ A (proj₁ p) (proj₁ q) , transˢ B (proj₂ p) (proj₂ q)
  }

map×⇒ : ∀ {A B C D} → A ⟶ B → C ⟶ D → (A ×S C) ⟶ (B ×S D)
map×⇒ f g = record
  { to = λ x → to f (proj₁ x) , to g (proj₂ x)
  ; resp = λ p → resp f (proj₁ p) , resp g (proj₂ p)
  }

data SumEq (A B : Setoid₀) : Carrier A ⊎ Carrier B → Carrier A ⊎ Carrier B → Set where
  inj₁≈ : ∀ {x y} → _≈_ A x y → SumEq A B (inj₁ x) (inj₁ y)
  inj₂≈ : ∀ {x y} → _≈_ B x y → SumEq A B (inj₂ x) (inj₂ y)

sum-refl : ∀ A B {x} → SumEq A B x x
sum-refl A B {inj₁ x} = inj₁≈ (reflˢ A)
sum-refl A B {inj₂ y} = inj₂≈ (reflˢ B)

sum-sym : ∀ A B {x y} → SumEq A B x y → SumEq A B y x
sum-sym A B (inj₁≈ p) = inj₁≈ (symˢ A p)
sum-sym A B (inj₂≈ p) = inj₂≈ (symˢ B p)

sum-trans : ∀ A B {x y z} → SumEq A B x y → SumEq A B y z → SumEq A B x z
sum-trans A B (inj₁≈ p) (inj₁≈ q) = inj₁≈ (transˢ A p q)
sum-trans A B (inj₂≈ p) (inj₂≈ q) = inj₂≈ (transˢ B p q)

_+S_ : Setoid₀ → Setoid₀ → Setoid₀
A +S B = record
  { Carrier = Carrier A ⊎ Carrier B
  ; _≈_ = SumEq A B
  ; reflˢ = sum-refl A B
  ; symˢ = sum-sym A B
  ; transˢ = sum-trans A B
  }

map+⇒ : ∀ {A B C D} → A ⟶ B → C ⟶ D → (A +S C) ⟶ (B +S D)
map+⇒ f g = record
  { to = λ { (inj₁ x) → inj₁ (to f x)
           ; (inj₂ y) → inj₂ (to g y)
           }
  ; resp = λ { (inj₁≈ p) → inj₁≈ (resp f p)
             ; (inj₂≈ p) → inj₂≈ (resp g p)
             }
  }

_⇒S_ : Setoid₀ → Setoid₀ → Setoid₀
A ⇒S B = record
  { Carrier = A ⟶ B
  ; _≈_ = _≈⇒_
  ; reflˢ = λ x → reflˢ B
  ; symˢ = λ p x → symˢ B (p x)
  ; transˢ = λ p q x → transˢ B (p x) (q x)
  }

----------------------------------------------------------------------
-- Generic open-code setoid semantics and W fixed points
----------------------------------------------------------------------

Env : Nat.ℕ → Set₁
Env n = Fin n → Setoid₀

ext : ∀ {n} → Env n → Setoid₀ → Env (Nat.suc n)
ext ρ X zero = X
ext ρ X (suc i) = ρ i

emptyEnv : Env 0
emptyEnv ()

data W {n} (D : Cont.Container (Nat.suc n)) : Set where
  sup : (s : Cont.Shape D) → (Cont.Position D s zero → W D) → W D

data WPos {n} (D : Cont.Container (Nat.suc n)) : W D → Fin n → Set where
  hereW : ∀ {s children i} →
          Cont.Position D s (suc i) →
          WPos D (sup s children) i
  belowW : ∀ {s children i} →
           (p : Cont.Position D s zero) →
           WPos D (children p) i →
           WPos D (sup s children) i

FixC : ∀ {n} → Cont.Container (Nat.suc n) → Cont.Container n
FixC D = record
  { Shape = W D
  ; Position = WPos D
  }

codeᵂ : ∀ {n} → Ty HO n → Cont.Container n
codeᵂ `𝟘 = Cont.zeroC
codeᵂ `𝟙 = Cont.oneC
codeᵂ (T `× U) = Cont._×C_ (codeᵂ T) (codeᵂ U)
codeᵂ (T `+ U) = Cont._+C_ (codeᵂ T) (codeᵂ U)
codeᵂ (T `⇒ U) = Cont.expC (codeᵂ T) (codeᵂ U)
codeᵂ (` i) = Cont.varC i
codeᵂ (ind G) = FixC (codeᵂ G)

data ValueEq {n} (C : Cont.Container n) (ρ : Env n) :
    Cont.Value C (λ i → Carrier (ρ i)) →
    Cont.Value C (λ i → Carrier (ρ i)) → Set where
  value≈ : ∀ {s xs ys} →
           ((i : Fin n) (p : Cont.Position C s i) →
             _≈_ (ρ i) (xs i p) (ys i p)) →
           ValueEq C ρ (s , xs) (s , ys)

value-refl : ∀ {n} (C : Cont.Container n) (ρ : Env n)
  {x : Cont.Value C (λ i → Carrier (ρ i))} → ValueEq C ρ x x
value-refl C ρ {s , xs} = value≈ λ i p → reflˢ (ρ i)

value-sym : ∀ {n} (C : Cont.Container n) (ρ : Env n)
  {x y : Cont.Value C (λ i → Carrier (ρ i))} →
  ValueEq C ρ x y → ValueEq C ρ y x
value-sym C ρ (value≈ p) = value≈ λ i q → symˢ (ρ i) (p i q)

value-trans : ∀ {n} (C : Cont.Container n) (ρ : Env n)
  {x y z : Cont.Value C (λ i → Carrier (ρ i))} →
  ValueEq C ρ x y → ValueEq C ρ y z → ValueEq C ρ x z
value-trans C ρ (value≈ p) (value≈ q) =
  value≈ λ i r → transˢ (ρ i) (p i r) (q i r)

value-pointwise : ∀ {n} {C : Cont.Container n} {ρ : Env n} {s xs ys} →
  ValueEq C ρ (s , xs) (s , ys) →
  (i : Fin n) (p : Cont.Position C s i) →
  _≈_ (ρ i) (xs i p) (ys i p)
value-pointwise (value≈ p) = p

ContainerS : ∀ {n} → Cont.Container n → Env n → Setoid₀
ContainerS C ρ = record
  { Carrier = Cont.Value C (λ i → Carrier (ρ i))
  ; _≈_ = ValueEq C ρ
  ; reflˢ = value-refl C ρ
  ; symˢ = value-sym C ρ
  ; transˢ = value-trans C ρ
  }

data FixEq {n} (D : Cont.Container (Nat.suc n)) (ρ : Env n) :
    Cont.Value (FixC D) (λ i → Carrier (ρ i)) →
    Cont.Value (FixC D) (λ i → Carrier (ρ i)) → Set where
  sup≈ : ∀ {s children children′ holes holes′} →
         ((p : Cont.Position D s zero) →
           FixEq D ρ
             (children p , λ i q → holes i (belowW p q))
             (children′ p , λ i q → holes′ i (belowW p q))) →
         ((i : Fin n) (p : Cont.Position D s (suc i)) →
           _≈_ (ρ i) (holes i (hereW p)) (holes′ i (hereW p))) →
         FixEq D ρ (sup s children , holes) (sup s children′ , holes′)

fix-refl-tree : ∀ {n} (D : Cont.Container (Nat.suc n)) (ρ : Env n)
  (tree : W D) →
  (holes : ∀ i → WPos D tree i → Carrier (ρ i)) →
  FixEq D ρ (tree , holes) (tree , holes)
fix-refl-tree D ρ (sup s children) holes =
  sup≈
    (λ p → fix-refl-tree D ρ (children p) (λ i q → holes i (belowW p q)))
    (λ i p → reflˢ (ρ i))

fix-refl : ∀ {n} (D : Cont.Container (Nat.suc n)) (ρ : Env n)
  {x : Cont.Value (FixC D) (λ i → Carrier (ρ i))} → FixEq D ρ x x
fix-refl D ρ {tree , holes} = fix-refl-tree D ρ tree holes

fix-sym : ∀ {n} (D : Cont.Container (Nat.suc n)) (ρ : Env n)
  {x y : Cont.Value (FixC D) (λ i → Carrier (ρ i))} →
  FixEq D ρ x y → FixEq D ρ y x
fix-sym D ρ (sup≈ children≈ holes≈) =
  sup≈
    (λ p → fix-sym D ρ (children≈ p))
    (λ i p → symˢ (ρ i) (holes≈ i p))

fix-trans : ∀ {n} (D : Cont.Container (Nat.suc n)) (ρ : Env n)
  {x y z : Cont.Value (FixC D) (λ i → Carrier (ρ i))} →
  FixEq D ρ x y → FixEq D ρ y z → FixEq D ρ x z
fix-trans D ρ (sup≈ children≈ holes≈) (sup≈ children≈′ holes≈′) =
  sup≈
    (λ p → fix-trans D ρ (children≈ p) (children≈′ p))
    (λ i p → transˢ (ρ i) (holes≈ i p) (holes≈′ i p))

valueFix→fixEq-tree : ∀ {n} (D : Cont.Container (Nat.suc n)) (ρ : Env n)
  (tree : W D)
  (xs ys : ∀ i → WPos D tree i → Carrier (ρ i)) →
  ((i : Fin n) (p : WPos D tree i) → _≈_ (ρ i) (xs i p) (ys i p)) →
  FixEq D ρ (tree , xs) (tree , ys)
valueFix→fixEq-tree D ρ (sup s children) xs ys pointwise =
  sup≈
    (λ p →
      valueFix→fixEq-tree D ρ (children p)
        (λ i q → xs i (belowW p q))
        (λ i q → ys i (belowW p q))
        (λ i q → pointwise i (belowW p q)))
    (λ i p → pointwise i (hereW p))

valueFix→fixEq : ∀ {n} (D : Cont.Container (Nat.suc n)) (ρ : Env n)
  {x y : Cont.Value (FixC D) (λ i → Carrier (ρ i))} →
  ValueEq (FixC D) ρ x y → FixEq D ρ x y
valueFix→fixEq D ρ {tree , xs} {.tree , ys} (value≈ pointwise) =
  valueFix→fixEq-tree D ρ tree xs ys pointwise

fix-empty-holes : (D : Cont.Container (Nat.suc Nat.zero)) (tree : W D)
  (holes holes′ : ∀ i → WPos D tree i → Carrier (emptyEnv i)) →
  FixEq D emptyEnv (tree , holes) (tree , holes′)
fix-empty-holes D (sup s children) holes holes′ =
  sup≈
    (λ p →
      fix-empty-holes D (children p)
        (λ i q → holes i (belowW p q))
        (λ i q → holes′ i (belowW p q)))
    (λ ())

FixS : ∀ {n} → Cont.Container (Nat.suc n) → Env n → Setoid₀
FixS D ρ = record
  { Carrier = Cont.Value (FixC D) (λ i → Carrier (ρ i))
  ; _≈_ = FixEq D ρ
  ; reflˢ = fix-refl D ρ
  ; symˢ = fix-sym D ρ
  ; transˢ = fix-trans D ρ
  }

forget-empty-holes : (D : Cont.Container (Nat.suc Nat.zero)) →
  (x : Carrier (FixS D emptyEnv)) →
  FixEq D emptyEnv x (proj₁ x , λ ())
forget-empty-holes D (tree , holes) = fix-empty-holes D tree holes (λ ())

fixEnv : ∀ {n} → Cont.Container (Nat.suc n) → Env n → Fin (Nat.suc n) → Set
fixEnv D ρ i = Carrier (ext ρ (FixS D ρ) i)

paraEnv : ∀ {n} → Cont.Container (Nat.suc n) → Env n → Set → Fin (Nat.suc n) → Set
paraEnv D ρ A zero = A × Carrier (FixS D ρ)
paraEnv D ρ A (suc i) = Carrier (ρ i)

rollC : ∀ {n} {D : Cont.Container (Nat.suc n)} {ρ : Env n} →
  Cont.Value D (fixEnv D ρ) →
  Carrier (FixS D ρ)
rollC (s , values) =
  sup s (λ p → proj₁ (values zero p)) ,
  λ
    { i (hereW p) → values (suc i) p
    ; i (belowW p q) → proj₂ (values zero p) i q
    }

outC : ∀ {n} {D : Cont.Container (Nat.suc n)} {ρ : Env n} →
  Carrier (FixS D ρ) →
  Cont.Value D (fixEnv D ρ)
outC (sup s children , holes) =
  s , λ
    { zero p → children p , λ i q → holes i (belowW p q)
    ; (suc i) p → holes i (hereW p)
    }

out-roll : ∀ {n} {D : Cont.Container (Nat.suc n)} {ρ : Env n}
  (layer : Cont.Value D (fixEnv D ρ)) →
  ValueEq D (ext ρ (FixS D ρ)) (outC (rollC layer)) layer
out-roll {D = D} {ρ = ρ} (s , values) =
  value≈ λ
    { zero p → fix-refl D ρ
    ; (suc i) p → reflˢ (ρ i)
    }

roll-out : ∀ {n} {D : Cont.Container (Nat.suc n)} {ρ : Env n}
  (x : Carrier (FixS D ρ)) →
  FixEq D ρ (rollC {D = D} {ρ = ρ} (outC {D = D} {ρ = ρ} x)) x
roll-out {D = D} {ρ = ρ} (sup s children , holes) =
  sup≈
    (λ p → fix-refl D ρ)
    (λ i p → reflˢ (ρ i))

paraLayerWith : ∀ {n} {D : Cont.Container (Nat.suc n)} {ρ : Env n} {A : Set}
  {s : Cont.Shape D}
  (children : Cont.Position D s zero → W D)
  (holes : ∀ i → WPos D (sup s children) i → Carrier (ρ i))
  (results : (p : Cont.Position D s zero) → A) →
  Cont.Value D (paraEnv D ρ A)
paraLayerWith {D = D} {ρ = ρ} {A = A} {s = s} children holes results = s , layer
  where
  layer : ∀ i → Cont.Position D s i →
          paraEnv D ρ A i
  layer zero p = results p , (children p , λ i q → holes i (belowW p q))
  layer (suc i) p = holes i (hereW p)

paraGo : ∀ {n} {D : Cont.Container (Nat.suc n)} {ρ : Env n} {A : Set} →
  (Cont.Value D (paraEnv D ρ A) → A) →
  (tree : W D) →
  (∀ i → WPos D tree i → Carrier (ρ i)) → A
paraGo {D = D} {ρ = ρ} {A = A} algebra (sup s children) holes =
  algebra (paraLayerWith {D = D} {ρ = ρ} {A = A} {s = s} children holes results)
  where
  results : (p : Cont.Position D s zero) → A
  results p = paraGo algebra (children p) child-holes
    where
    child-holes : ∀ i → WPos D (children p) i → Carrier (ρ i)
    child-holes i q = holes i (belowW p q)

paraC : ∀ {n} {D : Cont.Container (Nat.suc n)} {ρ : Env n} {A : Set} →
  (Cont.Value D (paraEnv D ρ A) → A) →
  Carrier (FixS D ρ) → A
paraC algebra (tree , holes) = paraGo algebra tree holes

paraLayerC : ∀ {n} {D : Cont.Container (Nat.suc n)} {ρ : Env n} {A : Set} →
  (Cont.Value D (paraEnv D ρ A) → A) →
  Carrier (FixS D ρ) →
  Cont.Value D (paraEnv D ρ A)
paraLayerC {D = D} {ρ = ρ} {A = A} algebra (sup s children , holes) =
  paraLayerWith {D = D} {ρ = ρ} {A = A} {s = s} children holes results
  where
  results : (p : Cont.Position D s zero) → A
  results p = paraGo algebra (children p) child-holes
    where
    child-holes : ∀ i → WPos D (children p) i → Carrier (ρ i)
    child-holes i q = holes i (belowW p q)

paraC-β : ∀ {n} {D : Cont.Container (Nat.suc n)} {ρ : Env n} {A : Set}
  (algebra : Cont.Value D (paraEnv D ρ A) → A)
  (x : Carrier (FixS D ρ)) →
  paraC algebra x ≡ algebra (paraLayerC algebra x)
paraC-β algebra (sup s children , holes) = refl

Semᵉ : ∀ {n} → Ty HO n → Env n → Setoid₀
Semᵉ `𝟘 ρ = ⊥S
Semᵉ `𝟙 ρ = ⊤S
Semᵉ (T `× U) ρ = Semᵉ T ρ ×S Semᵉ U ρ
Semᵉ (T `+ U) ρ = Semᵉ T ρ +S Semᵉ U ρ
Semᵉ (T `⇒ U) ρ = Semᵉ T emptyEnv ⇒S Semᵉ U ρ
Semᵉ (` i) ρ = ρ i
Semᵉ (ind G) ρ = FixS (codeᵂ G) ρ

Sem : TY HO → Setoid₀
Sem T = Semᵉ T emptyEnv

substEnv : ∀ {n m} → Sub HO n m → Env m → Env n
substEnv σ ρ i = Semᵉ (σ i) ρ

----------------------------------------------------------------------
-- Packing semantic layers as container layers
----------------------------------------------------------------------

postulate
  -- Needed to turn pointwise equality of raw Agda shape functions into
  -- propositional equality.
  funExt₀ : Extensionality Level.zero Level.zero

fix-shape-resp : ∀ {n} (D : Cont.Container (Nat.suc n)) (ρ : Env n)
  {x y : Carrier (FixS D ρ)} →
  FixEq D ρ x y →
  proj₁ x ≡ proj₁ y
fix-shape-resp D ρ (sup≈ children≈ holes≈) =
  cong sup-shape (funExt₀ λ p → fix-shape-resp D ρ (children≈ p))
  where
  sup-shape : (Cont.Position D _ zero → W D) → W D
  sup-shape children = sup _ children

fixEq-pointwise : ∀ {n} (D : Cont.Container (Nat.suc n)) (ρ : Env n)
  {tree : W D}
  {xs ys : ∀ i → WPos D tree i → Carrier (ρ i)} →
  FixEq D ρ (tree , xs) (tree , ys) →
  (i : Fin n) (p : WPos D tree i) →
  _≈_ (ρ i) (xs i p) (ys i p)
fixEq-pointwise D ρ (sup≈ children≈ holes≈) i (hereW p) =
  holes≈ i p
fixEq-pointwise D ρ (sup≈ children≈ holes≈) i (belowW p q) =
  fixEq-pointwise D ρ (children≈ p) i q

fixEq→valueEq : ∀ {n} (D : Cont.Container (Nat.suc n)) (ρ : Env n)
  {x y : Carrier (FixS D ρ)} →
  FixEq D ρ x y →
  ValueEq (FixC D) ρ x y
fixEq→valueEq D ρ {x = tree , xs} {y = tree′ , ys} tree≈
  with fix-shape-resp D ρ tree≈
... | refl = value≈ (fixEq-pointwise D ρ tree≈)

mutual
  closed→shape : (T : TY HO) → Carrier (Sem T) → Cont.Shape (codeᵂ T)
  closed→shape `𝟘 ()
  closed→shape `𝟙 tt = tt
  closed→shape (T `× U) (x , y) = closed→shape T x , closed→shape U y
  closed→shape (T `+ U) (inj₁ x) = inj₁ (closed→shape T x)
  closed→shape (T `+ U) (inj₂ y) = inj₂ (closed→shape U y)
  closed→shape (T `⇒ U) f =
    λ s → closed→shape U (to f (shape→closed T s))
  closed→shape (` ()) x
  closed→shape (ind G) x = proj₁ x

  shape→closed : (T : TY HO) → Cont.Shape (codeᵂ T) → Carrier (Sem T)
  shape→closed `𝟘 ()
  shape→closed `𝟙 tt = tt
  shape→closed (T `× U) (s , t) = shape→closed T s , shape→closed U t
  shape→closed (T `+ U) (inj₁ s) = inj₁ (shape→closed T s)
  shape→closed (T `+ U) (inj₂ t) = inj₂ (shape→closed U t)
  shape→closed (T `⇒ U) shape = record
    { to = λ x → shape→closed U (shape (closed→shape T x))
    ; resp = λ p →
        shape→closed-shape-resp U (cong shape (closed→shape-resp T p))
    }
  shape→closed (` ()) s
  shape→closed (ind G) tree = tree , λ ()

  shape→closed-shape-resp : (T : TY HO)
    {s t : Cont.Shape (codeᵂ T)} →
    s ≡ t →
    _≈_ (Sem T) (shape→closed T s) (shape→closed T t)
  shape→closed-shape-resp T refl = reflˢ (Sem T)

  closed→shape-resp : (T : TY HO) {x y : Carrier (Sem T)} →
    _≈_ (Sem T) x y →
    closed→shape T x ≡ closed→shape T y
  closed→shape-resp `𝟘 {x = ()}
  closed→shape-resp `𝟙 p = refl
  closed→shape-resp (T `× U) {x = x₁ , x₂} {y = y₁ , y₂} (p , q)
    with closed→shape T x₁ | closed→shape T y₁ | closed→shape-resp T p
       | closed→shape U x₂ | closed→shape U y₂ | closed→shape-resp U q
  ... | sx | .sx | refl | tx | .tx | refl = refl
  closed→shape-resp (T `+ U) {x = inj₁ x} {y = inj₁ y} (inj₁≈ p)
    with closed→shape T x | closed→shape T y | closed→shape-resp T p
  ... | sx | .sx | refl = refl
  closed→shape-resp (T `+ U) {x = inj₂ x} {y = inj₂ y} (inj₂≈ q)
    with closed→shape U x | closed→shape U y | closed→shape-resp U q
  ... | sx | .sx | refl = refl
  closed→shape-resp (T `⇒ U) p =
    funExt₀ λ s → closed→shape-resp U (p (shape→closed T s))
  closed→shape-resp (` ()) p
  closed→shape-resp (ind G) p = fix-shape-resp (codeᵂ G) emptyEnv p

  shape→closed→shape : (T : TY HO) →
    (s : Cont.Shape (codeᵂ T)) →
    closed→shape T (shape→closed T s) ≡ s
  shape→closed→shape `𝟘 ()
  shape→closed→shape `𝟙 tt = refl
  shape→closed→shape (T `× U) (s , t)
    rewrite shape→closed→shape T s
          | shape→closed→shape U t = refl
  shape→closed→shape (T `+ U) (inj₁ s)
    rewrite shape→closed→shape T s = refl
  shape→closed→shape (T `+ U) (inj₂ t)
    rewrite shape→closed→shape U t = refl
  shape→closed→shape (T `⇒ U) shape =
    funExt₀ λ s →
      trans
        (cong (λ t → closed→shape U (shape→closed U (shape t)))
          (shape→closed→shape T s))
        (shape→closed→shape U (shape s))
  shape→closed→shape (` ()) s
  shape→closed→shape (ind G) tree = refl

  closed→shape→closed : (T : TY HO) →
    (x : Carrier (Sem T)) →
    _≈_ (Sem T) (shape→closed T (closed→shape T x)) x
  closed→shape→closed `𝟘 ()
  closed→shape→closed `𝟙 tt = tt
  closed→shape→closed (T `× U) (x , y) =
    closed→shape→closed T x , closed→shape→closed U y
  closed→shape→closed (T `+ U) (inj₁ x) =
    inj₁≈ (closed→shape→closed T x)
  closed→shape→closed (T `+ U) (inj₂ y) =
    inj₂≈ (closed→shape→closed U y)
  closed→shape→closed (T `⇒ U) f x =
    transˢ (Sem U)
      (closed→shape→closed U (to f (shape→closed T (closed→shape T x))))
      (resp f (closed→shape→closed T x))
  closed→shape→closed (` ()) x
  closed→shape→closed (ind G) x =
    fix-sym (codeᵂ G) emptyEnv (forget-empty-holes (codeᵂ G) x)

packᵉ-to : ∀ {n} (G : Ty HO n) (ρ : Env n) →
  Carrier (Semᵉ G ρ) →
  Cont.Value (codeᵂ G) (λ i → Carrier (ρ i))
packᵉ-to `𝟘 ρ ()
packᵉ-to `𝟙 ρ tt = tt , λ _ ()
packᵉ-to (G `× H) ρ (x , y) with packᵉ-to G ρ x | packᵉ-to H ρ y
... | sx , xs | sy , ys =
  (sx , sy) , λ
    { i (inj₁ p) → xs i p
    ; i (inj₂ p) → ys i p
    }
packᵉ-to (G `+ H) ρ (inj₁ x) with packᵉ-to G ρ x
... | sx , xs = inj₁ sx , xs
packᵉ-to (G `+ H) ρ (inj₂ y) with packᵉ-to H ρ y
... | sy , ys = inj₂ sy , ys
packᵉ-to (A `⇒ G) ρ f =
  (λ a → proj₁ (packᵉ-to G ρ (to f (shape→closed A a)))) ,
  λ i p →
    proj₂ (packᵉ-to G ρ (to f (shape→closed A (proj₁ p)))) i (proj₂ p)
packᵉ-to (` i) ρ x = tt , λ { .i refl → x }
packᵉ-to (ind G) ρ x = x

pack-shape-closed : (T : TY HO) →
  (x : Carrier (Sem T)) →
  proj₁ (packᵉ-to T emptyEnv x) ≡ closed→shape T x
pack-shape-closed `𝟘 ()
pack-shape-closed `𝟙 tt = refl
pack-shape-closed (T `× U) (x , y)
  rewrite pack-shape-closed T x
        | pack-shape-closed U y = refl
pack-shape-closed (T `+ U) (inj₁ x)
  rewrite pack-shape-closed T x = refl
pack-shape-closed (T `+ U) (inj₂ y)
  rewrite pack-shape-closed U y = refl
pack-shape-closed (T `⇒ U) f =
  funExt₀ λ s → pack-shape-closed U (to f (shape→closed T s))
pack-shape-closed (` ()) x
pack-shape-closed (ind G) x = refl

pack-shape-shape→closed : (T : TY HO) →
  (s : Cont.Shape (codeᵂ T)) →
  proj₁ (packᵉ-to T emptyEnv (shape→closed T s)) ≡ s
pack-shape-shape→closed T s =
  trans (pack-shape-closed T (shape→closed T s)) (shape→closed→shape T s)

expValueEq : ∀ {n} (A : Cont.Container 0) (B : Cont.Container n) (ρ : Env n)
  {s t : Cont.Shape A → Cont.Shape B}
  {xs : ∀ i → Cont.Position (Cont.expC A B) s i → Carrier (ρ i)}
  {ys : ∀ i → Cont.Position (Cont.expC A B) t i → Carrier (ρ i)} →
  s ≡ t →
  ((a : Cont.Shape A) →
    ValueEq B ρ
      (s a , λ i p → xs i (a , p))
      (t a , λ i p → ys i (a , p))) →
  ValueEq (Cont.expC A B) ρ (s , xs) (t , ys)
expValueEq A B ρ refl pointwise =
  value≈ λ i (a , p) →
    value-pointwise (pointwise a) i p

packᵉ-ind-resp : ∀ {n} (G : Ty HO (Nat.suc n)) (ρ : Env n)
  {x y : Carrier (Semᵉ (ind G) ρ)} →
  _≈_ (Semᵉ (ind G) ρ) x y →
  ValueEq (codeᵂ (ind G)) ρ (packᵉ-to (ind G) ρ x) (packᵉ-to (ind G) ρ y)
packᵉ-ind-resp G ρ = fixEq→valueEq (codeᵂ G) ρ

mutual
  packᵉ-shape-resp : ∀ {n} (G : Ty HO n) (ρ : Env n)
    {x y : Carrier (Semᵉ G ρ)} →
    _≈_ (Semᵉ G ρ) x y →
    proj₁ (packᵉ-to G ρ x) ≡ proj₁ (packᵉ-to G ρ y)
  packᵉ-shape-resp G ρ {x = x} {y = y} p
    with packᵉ-to G ρ x | packᵉ-to G ρ y | packᵉ-resp G ρ p
  ... | sx , xs | .sx , ys | value≈ _ = refl

  packᵉ-⇒-resp : ∀ {n} (A : TY HO) (G : Ty HO n) (ρ : Env n)
    {f g : Carrier (Semᵉ (A `⇒ G) ρ)} →
    _≈_ (Semᵉ (A `⇒ G) ρ) f g →
    ValueEq (codeᵂ (A `⇒ G)) ρ (packᵉ-to (A `⇒ G) ρ f) (packᵉ-to (A `⇒ G) ρ g)
  packᵉ-⇒-resp A G ρ {f = f} {g = g} f≈g =
    expValueEq (codeᵂ A) (codeᵂ G) ρ
      (funExt₀ λ a → packᵉ-shape-resp G ρ (f≈g (shape→closed A a)))
      (λ a → packᵉ-resp G ρ (f≈g (shape→closed A a)))

  packᵉ-resp : ∀ {n} (G : Ty HO n) (ρ : Env n)
    {x y : Carrier (Semᵉ G ρ)} →
    _≈_ (Semᵉ G ρ) x y →
    ValueEq (codeᵂ G) ρ (packᵉ-to G ρ x) (packᵉ-to G ρ y)
  packᵉ-resp `𝟘 ρ {x = ()}
  packᵉ-resp `𝟙 ρ p = value≈ λ _ ()
  packᵉ-resp (G `× H) ρ {x = x₁ , x₂} {y = y₁ , y₂} (p , q)
    with packᵉ-to G ρ x₁ | packᵉ-to G ρ y₁ | packᵉ-resp G ρ p
       | packᵉ-to H ρ x₂ | packᵉ-to H ρ y₂ | packᵉ-resp H ρ q
  ... | sx , xs | .sx , ys | value≈ pg
      | tx , us | .tx , vs | value≈ ph =
    value≈ λ
      { i (inj₁ r) → pg i r
      ; i (inj₂ r) → ph i r
      }
  packᵉ-resp (G `+ H) ρ {x = inj₁ x} {y = inj₁ y} (inj₁≈ p)
    with packᵉ-to G ρ x | packᵉ-to G ρ y | packᵉ-resp G ρ p
  ... | sx , xs | .sx , ys | value≈ pg = value≈ pg
  packᵉ-resp (G `+ H) ρ {x = inj₂ x} {y = inj₂ y} (inj₂≈ p)
    with packᵉ-to H ρ x | packᵉ-to H ρ y | packᵉ-resp H ρ p
  ... | sx , xs | .sx , ys | value≈ ph = value≈ ph
  packᵉ-resp (A `⇒ G) ρ {x = f} {y = g} p =
    packᵉ-⇒-resp A G ρ {f = f} {g = g} p
  packᵉ-resp (` i) ρ p = value≈ λ { .i refl → p }
  packᵉ-resp (ind G) ρ {x = x} {y = y} p =
    packᵉ-ind-resp G ρ {x = x} {y = y} p

packᵉ : ∀ {n} (G : Ty HO n) (ρ : Env n) →
  Semᵉ G ρ ⟶ ContainerS (codeᵂ G) ρ
packᵉ G ρ = record
  { to = packᵉ-to G ρ
  ; resp = packᵉ-resp G ρ
  }

mutual
  unpackᵉ-to : ∀ {n} (G : Ty HO n) (ρ : Env n) →
    Cont.Value (codeᵂ G) (λ i → Carrier (ρ i)) →
    Carrier (Semᵉ G ρ)
  unpackᵉ-to `𝟘 ρ (() , values)
  unpackᵉ-to `𝟙 ρ (tt , values) = tt
  unpackᵉ-to (G `× H) ρ ((sx , sy) , values) =
    unpackᵉ-to G ρ (sx , λ i p → values i (inj₁ p)) ,
    unpackᵉ-to H ρ (sy , λ i p → values i (inj₂ p))
  unpackᵉ-to (G `+ H) ρ (inj₁ sx , values) =
    inj₁ (unpackᵉ-to G ρ (sx , values))
  unpackᵉ-to (G `+ H) ρ (inj₂ sy , values) =
    inj₂ (unpackᵉ-to H ρ (sy , values))
  unpackᵉ-to (A `⇒ G) ρ (shape , values) = record
    { to = λ x →
        unpackᵉ-to G ρ
          ( shape (proj₁ (packᵉ-to A emptyEnv x))
          , λ i p → values i (proj₁ (packᵉ-to A emptyEnv x) , p)
          )
    ; resp = unpackᵉ-exp-resp A G ρ shape values
    }
  unpackᵉ-to (` i) ρ (tt , values) = values i refl
  unpackᵉ-to (ind G) ρ x = x

  unpackᵉ-exp-resp : ∀ {n} (A : TY HO) (G : Ty HO n) (ρ : Env n)
    (shape : Cont.Shape (codeᵂ A) → Cont.Shape (codeᵂ G))
    (values : ∀ i →
      Cont.Position (codeᵂ (A `⇒ G)) shape i → Carrier (ρ i)) →
    {x y : Carrier (Sem A)} →
    _≈_ (Sem A) x y →
    _≈_ (Semᵉ G ρ)
      (unpackᵉ-to G ρ
        ( shape (proj₁ (packᵉ-to A emptyEnv x))
        , λ i p → values i (proj₁ (packᵉ-to A emptyEnv x) , p)
        ))
      (unpackᵉ-to G ρ
        ( shape (proj₁ (packᵉ-to A emptyEnv y))
        , λ i p → values i (proj₁ (packᵉ-to A emptyEnv y) , p)
        ))
  unpackᵉ-exp-resp A G ρ shape values {x} {y} x≈y
    with packᵉ-to A emptyEnv x | packᵉ-to A emptyEnv y | packᵉ-resp A emptyEnv x≈y
  ... | sx , xs | .sx , ys | value≈ pointwise =
    unpackᵉ-resp G ρ (value≈ λ i p → reflˢ (ρ i))

  unpackᵉ-resp : ∀ {n} (G : Ty HO n) (ρ : Env n)
    {x y : Cont.Value (codeᵂ G) (λ i → Carrier (ρ i))} →
    ValueEq (codeᵂ G) ρ x y →
    _≈_ (Semᵉ G ρ) (unpackᵉ-to G ρ x) (unpackᵉ-to G ρ y)
  unpackᵉ-resp `𝟘 ρ {() , xs} p
  unpackᵉ-resp `𝟙 ρ p = tt
  unpackᵉ-resp (G `× H) ρ (value≈ p) =
    unpackᵉ-resp G ρ (value≈ λ i q → p i (inj₁ q)) ,
    unpackᵉ-resp H ρ (value≈ λ i q → p i (inj₂ q))
  unpackᵉ-resp (G `+ H) ρ {inj₁ sx , xs} {inj₁ .sx , ys} (value≈ p) =
    inj₁≈ (unpackᵉ-resp G ρ (value≈ p))
  unpackᵉ-resp (G `+ H) ρ {inj₂ sy , xs} {inj₂ .sy , ys} (value≈ p) =
    inj₂≈ (unpackᵉ-resp H ρ (value≈ p))
  unpackᵉ-resp (A `⇒ G) ρ {shape , xs} { .shape , ys} (value≈ p) a =
    unpackᵉ-resp G ρ
      (value≈ λ i q → p i (proj₁ (packᵉ-to A emptyEnv a) , q))
  unpackᵉ-resp (` i) ρ (value≈ p) = p i refl
  unpackᵉ-resp (ind G) ρ p = valueFix→fixEq (codeᵂ G) ρ p

mutual
  pack-unpack-shapeᵉ : ∀ {n} (G : Ty HO n) (ρ : Env n)
    (v : Cont.Value (codeᵂ G) (λ i → Carrier (ρ i))) →
    proj₁ (packᵉ-to G ρ (unpackᵉ-to G ρ v)) ≡ proj₁ v
  pack-unpack-shapeᵉ `𝟘 ρ (() , values)
  pack-unpack-shapeᵉ `𝟙 ρ (tt , values) = refl
  pack-unpack-shapeᵉ (G `× H) ρ ((sx , sy) , values)
    rewrite pack-unpack-shapeᵉ G ρ (sx , λ i p → values i (inj₁ p))
          | pack-unpack-shapeᵉ H ρ (sy , λ i p → values i (inj₂ p)) = refl
  pack-unpack-shapeᵉ (G `+ H) ρ (inj₁ sx , values)
    rewrite pack-unpack-shapeᵉ G ρ (sx , values) = refl
  pack-unpack-shapeᵉ (G `+ H) ρ (inj₂ sy , values)
    rewrite pack-unpack-shapeᵉ H ρ (sy , values) = refl
  pack-unpack-shapeᵉ (A `⇒ G) ρ (shape , values) =
    funExt₀ λ a →
      trans
        (cong
          (λ b →
            proj₁ (packᵉ-to G ρ
              (unpackᵉ-to G ρ
                (shape b , λ i p → values i (b , p)))))
          (pack-shape-shape→closed A a))
        (pack-unpack-shapeᵉ G ρ (shape a , λ i p → values i (a , p)))
  pack-unpack-shapeᵉ (` i) ρ (tt , values) = refl
  pack-unpack-shapeᵉ (ind G) ρ v = refl

  pack-unpackᵉ : ∀ {n} (G : Ty HO n) (ρ : Env n)
    (v : Cont.Value (codeᵂ G) (λ i → Carrier (ρ i))) →
    ValueEq (codeᵂ G) ρ (packᵉ-to G ρ (unpackᵉ-to G ρ v)) v
  pack-unpackᵉ `𝟘 ρ (() , values)
  pack-unpackᵉ `𝟙 ρ (tt , values) = value≈ λ _ ()
  pack-unpackᵉ (G `× H) ρ ((sx , sy) , values)
    with packᵉ-to G ρ (unpackᵉ-to G ρ (sx , λ i p → values i (inj₁ p)))
       | pack-unpack-shapeᵉ G ρ (sx , λ i p → values i (inj₁ p))
       | pack-unpackᵉ G ρ (sx , λ i p → values i (inj₁ p))
  ... | .sx , xs | refl | pg
    with packᵉ-to H ρ (unpackᵉ-to H ρ (sy , λ i p → values i (inj₂ p)))
       | pack-unpack-shapeᵉ H ρ (sy , λ i p → values i (inj₂ p))
       | pack-unpackᵉ H ρ (sy , λ i p → values i (inj₂ p))
  ... | .sy , ys | refl | ph =
    value≈ λ
      { i (inj₁ p) → value-pointwise pg i p
      ; i (inj₂ p) → value-pointwise ph i p
      }
  pack-unpackᵉ (G `+ H) ρ (inj₁ sx , values)
    with packᵉ-to G ρ (unpackᵉ-to G ρ (sx , values))
       | pack-unpack-shapeᵉ G ρ (sx , values)
       | pack-unpackᵉ G ρ (sx , values)
  ... | .sx , xs | refl | pg =
    value≈ λ i p → value-pointwise pg i p
  pack-unpackᵉ (G `+ H) ρ (inj₂ sy , values)
    with packᵉ-to H ρ (unpackᵉ-to H ρ (sy , values))
       | pack-unpack-shapeᵉ H ρ (sy , values)
       | pack-unpackᵉ H ρ (sy , values)
  ... | .sy , ys | refl | ph =
    value≈ λ i p → value-pointwise ph i p
  pack-unpackᵉ (A `⇒ G) ρ (shape , values) =
    expValueEq (codeᵂ A) (codeᵂ G) ρ
      (funExt₀ λ a →
        trans
          (cong
            (λ b →
              proj₁ (packᵉ-to G ρ
                (unpackᵉ-to G ρ
                  (shape b , λ i p → values i (b , p)))))
            (pack-shape-shape→closed A a))
          (pack-unpack-shapeᵉ G ρ
            (shape a , λ i p → values i (a , p))))
      pointwise
    where
      pointwise : (a : Cont.Shape (codeᵂ A)) →
        ValueEq (codeᵂ G) ρ
          ( proj₁ (packᵉ-to G ρ
              (unpackᵉ-to G ρ
                ( shape (proj₁ (packᵉ-to A emptyEnv (shape→closed A a)))
                , λ i p →
                    values i
                      (proj₁ (packᵉ-to A emptyEnv (shape→closed A a)) , p)
                )))
          , λ i p →
              proj₂ (packᵉ-to G ρ
                (unpackᵉ-to G ρ
                  ( shape (proj₁ (packᵉ-to A emptyEnv (shape→closed A a)))
                  , λ j q →
                      values j
                        (proj₁ (packᵉ-to A emptyEnv (shape→closed A a)) , q)
                  ))) i p
          )
          (shape a , λ i p → values i (a , p))
      pointwise a rewrite pack-shape-shape→closed A a =
        pack-unpackᵉ G ρ (shape a , λ i p → values i (a , p))
  pack-unpackᵉ (` i) ρ (tt , values) = value≈ λ { .i refl → reflˢ (ρ i) }
  pack-unpackᵉ (ind G) ρ v = value-refl (FixC (codeᵂ G)) ρ

  unpack-packᵉ : ∀ {n} (G : Ty HO n) (ρ : Env n)
    (x : Carrier (Semᵉ G ρ)) →
    _≈_ (Semᵉ G ρ) (unpackᵉ-to G ρ (packᵉ-to G ρ x)) x
  unpack-packᵉ `𝟘 ρ ()
  unpack-packᵉ `𝟙 ρ tt = tt
  unpack-packᵉ (G `× H) ρ (x , y) =
    unpack-packᵉ G ρ x , unpack-packᵉ H ρ y
  unpack-packᵉ (G `+ H) ρ (inj₁ x) =
    inj₁≈ (unpack-packᵉ G ρ x)
  unpack-packᵉ (G `+ H) ρ (inj₂ y) =
    inj₂≈ (unpack-packᵉ H ρ y)
  unpack-packᵉ (A `⇒ G) ρ f x
    rewrite pack-shape-closed A x =
    transˢ (Semᵉ G ρ)
      (unpack-packᵉ G ρ (to f (shape→closed A (closed→shape A x))))
      (resp f (closed→shape→closed A x))
  unpack-packᵉ (` i) ρ x = reflˢ (ρ i)
  unpack-packᵉ (ind G) ρ x = fix-refl (codeᵂ G) ρ

----------------------------------------------------------------------
-- Functorial action and strength for open semantics
----------------------------------------------------------------------

EnvMap : ∀ {n} → Env n → Env n → Set
EnvMap ρ σ = ∀ i → ρ i ⟶ σ i

EnvMapEq : ∀ {n} {ρ σ : Env n} → EnvMap ρ σ → EnvMap ρ σ → Set
EnvMapEq η θ = ∀ i → _≈⇒_ (η i) (θ i)

EnvMapComp : ∀ {n} {ρ σ τ : Env n} →
  EnvMap ρ σ → EnvMap σ τ → EnvMap ρ τ → Set
EnvMapComp {τ = τ} η θ κ =
  ∀ i x → _≈_ (τ i) (to (θ i) (to (η i) x)) (to (κ i) x)

compEnvMap : ∀ {n} {ρ σ τ : Env n} →
  EnvMap ρ σ → EnvMap σ τ → EnvMap ρ τ
compEnvMap η θ i = θ i ∘⇒ η i

compEnvMap-comp : ∀ {n} {ρ σ τ : Env n}
  (η : EnvMap ρ σ) (θ : EnvMap σ τ) →
  EnvMapComp η θ (compEnvMap η θ)
compEnvMap-comp {τ = τ} η θ i x = reflˢ (τ i)

EnvMapRound : ∀ {n} {ρ σ : Env n} → EnvMap ρ σ → EnvMap σ ρ → Set
EnvMapRound {ρ = ρ} η θ =
  ∀ i x → _≈_ (ρ i) (to (θ i) (to (η i) x)) x

EnvMapId : ∀ {n} {ρ : Env n} → EnvMap ρ ρ → Set
EnvMapId {ρ = ρ} η =
  ∀ i x → _≈_ (ρ i) (to (η i) x) x

productEnv : ∀ {n} → Env n → Setoid₀ → Env n
productEnv ρ A i = ρ i ×S A

fstEnvMap : ∀ {n} (ρ : Env n) (A : Setoid₀) →
  EnvMap (productEnv ρ A) ρ
fstEnvMap ρ A i = record
  { to = proj₁
  ; resp = proj₁
  }

sndEnvMap : ∀ {n} (ρ : Env n) {A B : Setoid₀} →
  A ⟶ B → EnvMap (productEnv ρ A) (productEnv ρ B)
sndEnvMap ρ f i = map×⇒ (id⇒ {A = ρ i}) f

productEnvMap : ∀ {n} {ρ σ : Env n} →
  EnvMap ρ σ → (A : Setoid₀) → EnvMap (productEnv ρ A) (productEnv σ A)
productEnvMap η A i = map×⇒ (η i) (id⇒ {A = A})

mapFixEq : ∀ {n} (D : Cont.Container (Nat.suc n)) {ρ σ : Env n}
  (η : EnvMap ρ σ)
  {x y : Carrier (FixS D ρ)} →
  _≈_ (FixS D ρ) x y →
  _≈_ (FixS D σ)
    (proj₁ x , λ i p → to (η i) (proj₂ x i p))
    (proj₁ y , λ i p → to (η i) (proj₂ y i p))
mapFixEq D η (sup≈ children≈ holes≈) =
  sup≈
    (λ p → mapFixEq D η (children≈ p))
    (λ i p → resp (η i) (holes≈ i p))

mapFix : ∀ {n} (D : Cont.Container (Nat.suc n)) {ρ σ : Env n} →
  EnvMap ρ σ → FixS D ρ ⟶ FixS D σ
mapFix D η = record
  { to = λ x → proj₁ x , λ i p → to (η i) (proj₂ x i p)
  ; resp = mapFixEq D η
  }

mapFix-cong : ∀ {n} (D : Cont.Container (Nat.suc n)) {ρ σ : Env n}
  {η θ : EnvMap ρ σ} →
  EnvMapEq η θ →
  _≈⇒_ (mapFix D η) (mapFix D θ)
mapFix-cong D {σ = σ} η≈θ (tree , holes) =
  valueFix→fixEq D σ (value≈ λ i p → η≈θ i (holes i p))

mapFix-comp : ∀ {n} (D : Cont.Container (Nat.suc n)) {ρ σ τ : Env n}
  (η : EnvMap ρ σ) (θ : EnvMap σ τ) (κ : EnvMap ρ τ) →
  EnvMapComp η θ κ →
  _≈⇒_ (mapFix D θ ∘⇒ mapFix D η) (mapFix D κ)
mapFix-comp D {τ = τ} η θ κ comp (tree , holes) =
  valueFix→fixEq D τ (value≈ λ i p → comp i (holes i p))

mapFix-round : ∀ {n} (D : Cont.Container (Nat.suc n)) {ρ σ : Env n}
  (η : EnvMap ρ σ) (θ : EnvMap σ ρ) →
  EnvMapRound η θ →
  _≈⇒_ (mapFix D θ ∘⇒ mapFix D η) (id⇒ {A = FixS D ρ})
mapFix-round D η θ round (tree , holes) =
  valueFix→fixEq D _ (value≈ λ i p → round i (holes i p))

mapFix-id : ∀ {n} (D : Cont.Container (Nat.suc n)) {ρ : Env n}
  (η : EnvMap ρ ρ) →
  EnvMapId η →
  _≈⇒_ (mapFix D η) (id⇒ {A = FixS D ρ})
mapFix-id D η η-id (tree , holes) =
  valueFix→fixEq D _ (value≈ λ i p → η-id i (holes i p))

mapᵉ : ∀ {n} (G : Ty HO n) {ρ σ : Env n} →
  EnvMap ρ σ → Semᵉ G ρ ⟶ Semᵉ G σ
mapᵉ `𝟘 η = record
  { to = λ ()
  ; resp = λ {}
  }
mapᵉ `𝟙 η = record
  { to = λ _ → tt
  ; resp = λ _ → tt
  }
mapᵉ (G `× H) η = record
  { to = λ x → to (mapᵉ G η) (proj₁ x) , to (mapᵉ H η) (proj₂ x)
  ; resp = λ p → resp (mapᵉ G η) (proj₁ p) , resp (mapᵉ H η) (proj₂ p)
  }
mapᵉ (G `+ H) η = record
  { to = λ { (inj₁ x) → inj₁ (to (mapᵉ G η) x)
           ; (inj₂ y) → inj₂ (to (mapᵉ H η) y)
           }
  ; resp = λ { (inj₁≈ p) → inj₁≈ (resp (mapᵉ G η) p)
             ; (inj₂≈ p) → inj₂≈ (resp (mapᵉ H η) p)
             }
  }
mapᵉ (A `⇒ G) η = record
  { to = λ f → record
      { to = λ x → to (mapᵉ G η) (to f x)
      ; resp = λ p → resp (mapᵉ G η) (resp f p)
      }
  ; resp = λ p x → resp (mapᵉ G η) (p x)
  }
mapᵉ (` i) η = η i
mapᵉ (ind G) η = mapFix (codeᵂ G) η

mapᵉ-cong : ∀ {n} (G : Ty HO n) {ρ σ : Env n}
  {η θ : EnvMap ρ σ} →
  EnvMapEq η θ →
  _≈⇒_ (mapᵉ G η) (mapᵉ G θ)
mapᵉ-cong `𝟘 η≈θ ()
mapᵉ-cong `𝟙 η≈θ x = tt
mapᵉ-cong (G `× H) η≈θ x =
  mapᵉ-cong G η≈θ (proj₁ x) ,
  mapᵉ-cong H η≈θ (proj₂ x)
mapᵉ-cong (G `+ H) η≈θ (inj₁ x) =
  inj₁≈ (mapᵉ-cong G η≈θ x)
mapᵉ-cong (G `+ H) η≈θ (inj₂ y) =
  inj₂≈ (mapᵉ-cong H η≈θ y)
mapᵉ-cong (A `⇒ G) η≈θ f x =
  mapᵉ-cong G η≈θ (to f x)
mapᵉ-cong (` i) η≈θ x = η≈θ i x
mapᵉ-cong (ind G) {ρ = ρ} {σ = σ} {η = η} {θ = θ} η≈θ x =
  mapFix-cong (codeᵂ G) {ρ = ρ} {σ = σ} {η = η} {θ = θ} η≈θ x

mapᵉ-comp : ∀ {n} (G : Ty HO n) {ρ σ τ : Env n}
  (η : EnvMap ρ σ) (θ : EnvMap σ τ) (κ : EnvMap ρ τ) →
  EnvMapComp η θ κ →
  _≈⇒_ (mapᵉ G θ ∘⇒ mapᵉ G η) (mapᵉ G κ)
mapᵉ-comp `𝟘 η θ κ comp ()
mapᵉ-comp `𝟙 η θ κ comp x = tt
mapᵉ-comp (G `× H) η θ κ comp x =
  mapᵉ-comp G η θ κ comp (proj₁ x) ,
  mapᵉ-comp H η θ κ comp (proj₂ x)
mapᵉ-comp (G `+ H) η θ κ comp (inj₁ x) =
  inj₁≈ (mapᵉ-comp G η θ κ comp x)
mapᵉ-comp (G `+ H) η θ κ comp (inj₂ y) =
  inj₂≈ (mapᵉ-comp H η θ κ comp y)
mapᵉ-comp (A `⇒ G) η θ κ comp f x =
  mapᵉ-comp G η θ κ comp (to f x)
mapᵉ-comp (` i) η θ κ comp x = comp i x
mapᵉ-comp (ind G) η θ κ comp x =
  mapFix-comp (codeᵂ G) η θ κ comp x

mapᵉ-round : ∀ {n} (G : Ty HO n) {ρ σ : Env n}
  (η : EnvMap ρ σ) (θ : EnvMap σ ρ) →
  EnvMapRound η θ →
  _≈⇒_ (mapᵉ G θ ∘⇒ mapᵉ G η) (id⇒ {A = Semᵉ G ρ})
mapᵉ-round `𝟘 η θ round ()
mapᵉ-round `𝟙 η θ round x = tt
mapᵉ-round (G `× H) η θ round x =
  mapᵉ-round G η θ round (proj₁ x) ,
  mapᵉ-round H η θ round (proj₂ x)
mapᵉ-round (G `+ H) η θ round (inj₁ x) =
  inj₁≈ (mapᵉ-round G η θ round x)
mapᵉ-round (G `+ H) η θ round (inj₂ y) =
  inj₂≈ (mapᵉ-round H η θ round y)
mapᵉ-round (A `⇒ G) η θ round f x =
  mapᵉ-round G η θ round (to f x)
mapᵉ-round (` i) η θ round x = round i x
mapᵉ-round (ind G) η θ round x =
  mapFix-round (codeᵂ G) η θ round x

mapᵉ-id : ∀ {n} (G : Ty HO n) {ρ : Env n}
  (η : EnvMap ρ ρ) →
  EnvMapId η →
  _≈⇒_ (mapᵉ G η) (id⇒ {A = Semᵉ G ρ})
mapᵉ-id `𝟘 η η-id ()
mapᵉ-id `𝟙 η η-id x = tt
mapᵉ-id (G `× H) η η-id x =
  mapᵉ-id G η η-id (proj₁ x) ,
  mapᵉ-id H η η-id (proj₂ x)
mapᵉ-id (G `+ H) η η-id (inj₁ x) =
  inj₁≈ (mapᵉ-id G η η-id x)
mapᵉ-id (G `+ H) η η-id (inj₂ y) =
  inj₂≈ (mapᵉ-id H η η-id y)
mapᵉ-id (A `⇒ G) η η-id f x =
  mapᵉ-id G η η-id (to f x)
mapᵉ-id (` i) η η-id x = η-id i x
mapᵉ-id (ind G) η η-id x =
  mapFix-id (codeᵂ G) η η-id x

paraLayerFix : ∀ {n} {D : Cont.Container (Nat.suc n)} {ρ : Env n} {A : Set} →
  Cont.Value D (paraEnv D ρ A) →
  Cont.Value D (fixEnv D ρ)
paraLayerFix (s , values) =
  s , λ
    { zero p → proj₂ (values zero p)
    ; (suc i) p → values (suc i) p
    }

paraLayerFix-out : ∀ {n} {D : Cont.Container (Nat.suc n)} {ρ : Env n} {A : Set}
  {s : Cont.Shape D}
  (children : Cont.Position D s zero → W D)
  (holes : ∀ i → WPos D (sup s children) i → Carrier (ρ i))
  (results : Cont.Position D s zero → A) →
  ValueEq D (ext ρ (FixS D ρ))
    (paraLayerFix (paraLayerWith {D = D} {ρ = ρ} {A = A} {s = s}
      children holes results))
    (outC (sup s children , holes))
paraLayerFix-out {D = D} {ρ = ρ} children holes results =
  value≈ λ
    { zero p → fix-refl D ρ
    ; (suc i) p → reflˢ (ρ i)
    }

paraLayerFix-paraLayerC-out : ∀ {n} {D : Cont.Container (Nat.suc n)}
  {ρ : Env n} {A : Set}
  (algebra : Cont.Value D (paraEnv D ρ A) → A)
  (x : Carrier (FixS D ρ)) →
  ValueEq D (ext ρ (FixS D ρ))
    (paraLayerFix (paraLayerC algebra x))
    (outC x)
paraLayerFix-paraLayerC-out algebra (sup s children , holes) =
  paraLayerFix-out children holes
    (λ p → paraGo algebra (children p) (λ i q → holes i (belowW p q)))

rollC-resp : ∀ {n} {D : Cont.Container (Nat.suc n)} {ρ : Env n}
  {x y : Cont.Value D (fixEnv D ρ)} →
  ValueEq D (ext ρ (FixS D ρ)) x y →
  _≈_ (FixS D ρ) (rollC x) (rollC y)
rollC-resp {x = s , xs} {y = .s , ys} (value≈ p) =
  sup≈
    (λ q → p zero q)
    (λ i q → p (suc i) q)

wkSub : ∀ {m} → Sub HO m (Nat.suc m)
wkSub i = ` (suc i)

varSub : ∀ {n m} → Ren n m → Sub HO n m
varSub ρ i = ` (ρ i)

extˢ-cong : ∀ {n m} {σ τ : Sub HO n m} →
  (∀ i → σ i ≡ τ i) →
  ∀ i → extˢ σ i ≡ extˢ τ i
extˢ-cong pointwise zero = refl
extˢ-cong pointwise (suc i) = cong (ren suc) (pointwise i)

sub-cong : ∀ {n m} {σ τ : Sub HO n m} →
  (∀ i → σ i ≡ τ i) →
  (T : Ty HO n) →
  sub σ T ≡ sub τ T
sub-cong pointwise `𝟘 = refl
sub-cong pointwise `𝟙 = refl
sub-cong pointwise (T `× U) =
  cong₂ _`×_ (sub-cong pointwise T) (sub-cong pointwise U)
sub-cong pointwise (T `+ U) =
  cong₂ _`+_ (sub-cong pointwise T) (sub-cong pointwise U)
sub-cong pointwise (T `⇒ U) =
  cong (T `⇒_) (sub-cong pointwise U)
sub-cong pointwise (` i) = pointwise i
sub-cong pointwise (ind G) =
  cong ind (sub-cong (extˢ-cong pointwise) G)

varSub-extᴿ : ∀ {n m} (ρ : Ren n m) →
  ∀ i → varSub (extᴿ ρ) i ≡ extˢ (varSub ρ) i
varSub-extᴿ ρ zero = refl
varSub-extᴿ ρ (suc i) = refl

ren≡sub-varSub : ∀ {n m} (ρ : Ren n m) (T : Ty HO n) →
  ren ρ T ≡ sub (varSub ρ) T
ren≡sub-varSub ρ `𝟘 = refl
ren≡sub-varSub ρ `𝟙 = refl
ren≡sub-varSub ρ (T `× U) =
  cong₂ _`×_ (ren≡sub-varSub ρ T) (ren≡sub-varSub ρ U)
ren≡sub-varSub ρ (T `+ U) =
  cong₂ _`+_ (ren≡sub-varSub ρ T) (ren≡sub-varSub ρ U)
ren≡sub-varSub ρ (T `⇒ U) =
  cong (T `⇒_) (ren≡sub-varSub ρ U)
ren≡sub-varSub ρ (` i) = refl
ren≡sub-varSub ρ (ind G) =
  cong ind
    (trans
      (ren≡sub-varSub (extᴿ ρ) G)
      (sub-cong (varSub-extᴿ ρ) G))

substSourceEnv : ∀ {n m} (G : Ty HO (Nat.suc n)) →
  Sub HO n m → Env m → Env (Nat.suc m)
substSourceEnv G σ ρ =
  ext ρ (FixS (codeᵂ (sub (extˢ σ) G)) ρ)

substTargetEnv : ∀ {n m} (G : Ty HO (Nat.suc n)) →
  Sub HO n m → Env m → Env (Nat.suc n)
substTargetEnv G σ ρ =
  ext (substEnv σ ρ) (FixS (codeᵂ G) (substEnv σ ρ))

{-# TERMINATING #-}
mutual
  weaken→ᵉ : ∀ {m} (T : Ty HO m) (ρ : Env m) (X : Setoid₀) →
    Semᵉ (ren suc T) (ext ρ X) ⟶ Semᵉ T ρ
  weaken→ᵉ T ρ X =
    Eq.subst
      (λ S → Semᵉ S (ext ρ X) ⟶ Semᵉ T ρ)
      (sym (ren≡sub-varSub suc T))
      (subst→ᵉ T wkSub (ext ρ X))

  weaken←ᵉ : ∀ {m} (T : Ty HO m) (ρ : Env m) (X : Setoid₀) →
    Semᵉ T ρ ⟶ Semᵉ (ren suc T) (ext ρ X)
  weaken←ᵉ T ρ X =
    Eq.subst
      (λ S → Semᵉ T ρ ⟶ Semᵉ S (ext ρ X))
      (sym (ren≡sub-varSub suc T))
      (subst←ᵉ T wkSub (ext ρ X))

  substFixEnv→ : ∀ {n m} (G : Ty HO (Nat.suc n)) (σ : Sub HO n m) (ρ : Env m) →
    EnvMap
      (substEnv (extˢ σ) (substSourceEnv G σ ρ))
      (substTargetEnv G σ ρ)
  substFixEnv→ G σ ρ zero = substFix→ᵉ G σ ρ
  substFixEnv→ G σ ρ (suc i) =
    weaken→ᵉ (σ i) ρ (FixS (codeᵂ (sub (extˢ σ) G)) ρ)

  substFixEnv← : ∀ {n m} (G : Ty HO (Nat.suc n)) (σ : Sub HO n m) (ρ : Env m) →
    EnvMap
      (substTargetEnv G σ ρ)
      (substEnv (extˢ σ) (substSourceEnv G σ ρ))
  substFixEnv← G σ ρ zero = substFix←ᵉ G σ ρ
  substFixEnv← G σ ρ (suc i) =
    weaken←ᵉ (σ i) ρ (FixS (codeᵂ (sub (extˢ σ) G)) ρ)

  substLayer→ : ∀ {n m} (G : Ty HO (Nat.suc n)) (σ : Sub HO n m) (ρ : Env m) →
    Cont.Value (codeᵂ (sub (extˢ σ) G)) (fixEnv (codeᵂ (sub (extˢ σ) G)) ρ) →
    Cont.Value (codeᵂ G) (fixEnv (codeᵂ G) (substEnv σ ρ))
  substLayer→ G σ ρ layer =
    to (packᵉ G (substTargetEnv G σ ρ))
      (to (mapᵉ G (substFixEnv→ G σ ρ))
        (to (subst→ᵉ G (extˢ σ) (substSourceEnv G σ ρ))
          (unpackᵉ-to (sub (extˢ σ) G) (substSourceEnv G σ ρ) layer)))

  substLayer← : ∀ {n m} (G : Ty HO (Nat.suc n)) (σ : Sub HO n m) (ρ : Env m) →
    Cont.Value (codeᵂ G) (fixEnv (codeᵂ G) (substEnv σ ρ)) →
    Cont.Value (codeᵂ (sub (extˢ σ) G)) (fixEnv (codeᵂ (sub (extˢ σ) G)) ρ)
  substLayer← G σ ρ layer =
    to (packᵉ (sub (extˢ σ) G) (substSourceEnv G σ ρ))
      (to (subst←ᵉ G (extˢ σ) (substSourceEnv G σ ρ))
        (to (mapᵉ G (substFixEnv← G σ ρ))
          (unpackᵉ-to G (substTargetEnv G σ ρ) layer)))

  substFix→-alg : ∀ {n m} (G : Ty HO (Nat.suc n)) (σ : Sub HO n m) (ρ : Env m) →
    Cont.Value (codeᵂ (sub (extˢ σ) G))
      (paraEnv (codeᵂ (sub (extˢ σ) G)) ρ
        (Carrier (FixS (codeᵂ G) (substEnv σ ρ)))) →
    Carrier (FixS (codeᵂ G) (substEnv σ ρ))
  substFix→-alg G σ ρ layer =
    rollC (substLayer→ G σ ρ (paraLayerFix layer))

  substFix←-alg : ∀ {n m} (G : Ty HO (Nat.suc n)) (σ : Sub HO n m) (ρ : Env m) →
    Cont.Value (codeᵂ G)
      (paraEnv (codeᵂ G) (substEnv σ ρ)
        (Carrier (FixS (codeᵂ (sub (extˢ σ) G)) ρ))) →
    Carrier (FixS (codeᵂ (sub (extˢ σ) G)) ρ)
  substFix←-alg G σ ρ layer =
    rollC (substLayer← G σ ρ (paraLayerFix layer))

  substFix→-to : ∀ {n m} (G : Ty HO (Nat.suc n)) (σ : Sub HO n m) (ρ : Env m) →
    Carrier (FixS (codeᵂ (sub (extˢ σ) G)) ρ) →
    Carrier (FixS (codeᵂ G) (substEnv σ ρ))
  substFix→-to G σ ρ = paraC (substFix→-alg G σ ρ)

  substFix←-to : ∀ {n m} (G : Ty HO (Nat.suc n)) (σ : Sub HO n m) (ρ : Env m) →
    Carrier (FixS (codeᵂ G) (substEnv σ ρ)) →
    Carrier (FixS (codeᵂ (sub (extˢ σ) G)) ρ)
  substFix←-to G σ ρ = paraC (substFix←-alg G σ ρ)

  substFix→-resp : ∀ {n m} (G : Ty HO (Nat.suc n)) (σ : Sub HO n m) (ρ : Env m)
    {x y : Carrier (FixS (codeᵂ (sub (extˢ σ) G)) ρ)} →
    _≈_ (FixS (codeᵂ (sub (extˢ σ) G)) ρ) x y →
    _≈_ (FixS (codeᵂ G) (substEnv σ ρ))
      (substFix→-to G σ ρ x) (substFix→-to G σ ρ y)
  substFix→-resp G σ ρ {x = sup s children , holes}
    {y = sup .s children′ , holes′} (sup≈ children≈ holes≈) =
    rollC-resp
      (packᵉ-resp G (substTargetEnv G σ ρ)
        (resp (mapᵉ G (substFixEnv→ G σ ρ))
          (resp (subst→ᵉ G (extˢ σ) (substSourceEnv G σ ρ))
            (unpackᵉ-resp (sub (extˢ σ) G) (substSourceEnv G σ ρ)
              (value≈ λ
                { zero p → children≈ p
                ; (suc i) p → holes≈ i p
                })))))

  substFix←-resp : ∀ {n m} (G : Ty HO (Nat.suc n)) (σ : Sub HO n m) (ρ : Env m)
    {x y : Carrier (FixS (codeᵂ G) (substEnv σ ρ))} →
    _≈_ (FixS (codeᵂ G) (substEnv σ ρ)) x y →
    _≈_ (FixS (codeᵂ (sub (extˢ σ) G)) ρ)
      (substFix←-to G σ ρ x) (substFix←-to G σ ρ y)
  substFix←-resp G σ ρ {x = sup s children , holes}
    {y = sup .s children′ , holes′} (sup≈ children≈ holes≈) =
    rollC-resp
      (packᵉ-resp (sub (extˢ σ) G) (substSourceEnv G σ ρ)
        (resp (subst←ᵉ G (extˢ σ) (substSourceEnv G σ ρ))
          (resp (mapᵉ G (substFixEnv← G σ ρ))
            (unpackᵉ-resp G (substTargetEnv G σ ρ)
              (value≈ λ
                { zero p → children≈ p
                ; (suc i) p → holes≈ i p
                })))))

  substFix→ᵉ : ∀ {n m} (G : Ty HO (Nat.suc n)) (σ : Sub HO n m) (ρ : Env m) →
    Semᵉ (sub σ (ind G)) ρ ⟶ Semᵉ (ind G) (substEnv σ ρ)
  substFix→ᵉ G σ ρ = record
    { to = substFix→-to G σ ρ
    ; resp = substFix→-resp G σ ρ
    }

  substFix←ᵉ : ∀ {n m} (G : Ty HO (Nat.suc n)) (σ : Sub HO n m) (ρ : Env m) →
    Semᵉ (ind G) (substEnv σ ρ) ⟶ Semᵉ (sub σ (ind G)) ρ
  substFix←ᵉ G σ ρ = record
    { to = substFix←-to G σ ρ
    ; resp = substFix←-resp G σ ρ
    }

  subst→ᵉ : ∀ {n m} (G : Ty HO n) (σ : Sub HO n m) (ρ : Env m) →
    Semᵉ (sub σ G) ρ ⟶ Semᵉ G (substEnv σ ρ)
  subst→ᵉ `𝟘 σ ρ = id⇒
  subst→ᵉ `𝟙 σ ρ = id⇒
  subst→ᵉ (G `× H) σ ρ = map×⇒ (subst→ᵉ G σ ρ) (subst→ᵉ H σ ρ)
  subst→ᵉ (G `+ H) σ ρ = map+⇒ (subst→ᵉ G σ ρ) (subst→ᵉ H σ ρ)
  subst→ᵉ (A `⇒ G) σ ρ = record
    { to = λ f → record
        { to = λ x → to (subst→ᵉ G σ ρ) (to f x)
        ; resp = λ p → resp (subst→ᵉ G σ ρ) (resp f p)
        }
    ; resp = λ p x → resp (subst→ᵉ G σ ρ) (p x)
    }
  subst→ᵉ (` i) σ ρ = id⇒
  subst→ᵉ (ind G) σ ρ = substFix→ᵉ G σ ρ

  subst←ᵉ : ∀ {n m} (G : Ty HO n) (σ : Sub HO n m) (ρ : Env m) →
    Semᵉ G (substEnv σ ρ) ⟶ Semᵉ (sub σ G) ρ
  subst←ᵉ `𝟘 σ ρ = id⇒
  subst←ᵉ `𝟙 σ ρ = id⇒
  subst←ᵉ (G `× H) σ ρ = map×⇒ (subst←ᵉ G σ ρ) (subst←ᵉ H σ ρ)
  subst←ᵉ (G `+ H) σ ρ = map+⇒ (subst←ᵉ G σ ρ) (subst←ᵉ H σ ρ)
  subst←ᵉ (A `⇒ G) σ ρ = record
    { to = λ f → record
        { to = λ x → to (subst←ᵉ G σ ρ) (to f x)
        ; resp = λ p → resp (subst←ᵉ G σ ρ) (resp f p)
        }
    ; resp = λ p x → resp (subst←ᵉ G σ ρ) (p x)
    }
  subst←ᵉ (` i) σ ρ = id⇒
  subst←ᵉ (ind G) σ ρ = substFix←ᵉ G σ ρ

  weaken-round-helper : ∀ {m} (T : Ty HO m) (ρ : Env m) (X : Setoid₀)
    {S : Ty HO (Nat.suc m)} →
    (e : S ≡ sub wkSub T) →
    _≈⇒_
      ( Eq.subst
          (λ R → Semᵉ T ρ ⟶ Semᵉ R (ext ρ X))
          (sym e)
          (subst←ᵉ T wkSub (ext ρ X))
        ∘⇒
        Eq.subst
          (λ R → Semᵉ R (ext ρ X) ⟶ Semᵉ T ρ)
          (sym e)
          (subst→ᵉ T wkSub (ext ρ X))
      )
      (id⇒ {A = Semᵉ S (ext ρ X)})
  weaken-round-helper T ρ X refl =
    subst-round←→ T wkSub (ext ρ X)

  weaken-round←→ : ∀ {m} (T : Ty HO m) (ρ : Env m) (X : Setoid₀) →
    _≈⇒_ (weaken←ᵉ T ρ X ∘⇒ weaken→ᵉ T ρ X)
          (id⇒ {A = Semᵉ (ren suc T) (ext ρ X)})
  weaken-round←→ T ρ X =
    weaken-round-helper T ρ X (ren≡sub-varSub suc T)

  substFixEnv-round←→ : ∀ {n m} (G : Ty HO (Nat.suc n))
    (σ : Sub HO n m) (ρ : Env m) →
    EnvMapRound (substFixEnv→ G σ ρ) (substFixEnv← G σ ρ)
  substFixEnv-round←→ G σ ρ zero =
    substFix-round←→ G σ ρ
  substFixEnv-round←→ G σ ρ (suc i) =
    weaken-round←→ (σ i) ρ (FixS (codeᵂ (sub (extˢ σ) G)) ρ)

  substLayer←-resp : ∀ {n m} (G : Ty HO (Nat.suc n))
    (σ : Sub HO n m) (ρ : Env m)
    {layer layer′ : Cont.Value (codeᵂ G)
      (fixEnv (codeᵂ G) (substEnv σ ρ))} →
    ValueEq (codeᵂ G) (substTargetEnv G σ ρ) layer layer′ →
    ValueEq (codeᵂ (sub (extˢ σ) G)) (substSourceEnv G σ ρ)
      (substLayer← G σ ρ layer)
      (substLayer← G σ ρ layer′)
  substLayer←-resp G σ ρ layer≈ =
    packᵉ-resp (sub (extˢ σ) G) (substSourceEnv G σ ρ)
      (resp (subst←ᵉ G (extˢ σ) (substSourceEnv G σ ρ))
        (resp (mapᵉ G (substFixEnv← G σ ρ))
          (unpackᵉ-resp G (substTargetEnv G σ ρ) layer≈)))

  substLayer-round←→ : ∀ {n m} (G : Ty HO (Nat.suc n))
    (σ : Sub HO n m) (ρ : Env m)
    (layer : Cont.Value (codeᵂ (sub (extˢ σ) G))
      (fixEnv (codeᵂ (sub (extˢ σ) G)) ρ)) →
    ValueEq (codeᵂ (sub (extˢ σ) G)) (substSourceEnv G σ ρ)
      (substLayer← G σ ρ (substLayer→ G σ ρ layer))
      layer
  substLayer-round←→ G σ ρ layer =
    value-trans (codeᵂ (sub (extˢ σ) G)) (substSourceEnv G σ ρ)
      (packᵉ-resp (sub (extˢ σ) G) (substSourceEnv G σ ρ) semantic-round)
      (pack-unpackᵉ (sub (extˢ σ) G) (substSourceEnv G σ ρ) layer)
    where
      source : Env _
      source = substSourceEnv G σ ρ

      target : Env _
      target = substTargetEnv G σ ρ

      unpacked : Carrier (Semᵉ (sub (extˢ σ) G) source)
      unpacked = unpackᵉ-to (sub (extˢ σ) G) source layer

      substituted : Carrier (Semᵉ G target)
      substituted =
        to (mapᵉ G (substFixEnv→ G σ ρ))
          (to (subst→ᵉ G (extˢ σ) source) unpacked)

      semantic-round : _≈_ (Semᵉ (sub (extˢ σ) G) source)
        ( to (subst←ᵉ G (extˢ σ) source)
          (to (mapᵉ G (substFixEnv← G σ ρ))
            (unpackᵉ-to G target (packᵉ-to G target substituted)))
        )
        unpacked
      semantic-round =
        transˢ (Semᵉ (sub (extˢ σ) G) source)
          (resp (subst←ᵉ G (extˢ σ) source)
            (transˢ (Semᵉ G (substEnv (extˢ σ) source))
              (resp (mapᵉ G (substFixEnv← G σ ρ))
                (unpack-packᵉ G target substituted))
              (mapᵉ-round G
                (substFixEnv→ G σ ρ)
                (substFixEnv← G σ ρ)
                (substFixEnv-round←→ G σ ρ)
                (to (subst→ᵉ G (extˢ σ) source) unpacked))))
          (subst-round←→ G (extˢ σ) source unpacked)

  substFix-round←→ : ∀ {n m} (G : Ty HO (Nat.suc n))
    (σ : Sub HO n m) (ρ : Env m) →
    _≈⇒_ (substFix←ᵉ G σ ρ ∘⇒ substFix→ᵉ G σ ρ)
          (id⇒ {A = FixS (codeᵂ (sub (extˢ σ) G)) ρ})
  substFix-round←→ G σ ρ (sup s children , holes) =
    transˢ (FixS (codeᵂ (sub (extˢ σ) G)) ρ)
      (rollC-resp
        (value-trans (codeᵂ (sub (extˢ σ) G)) (substSourceEnv G σ ρ)
          (substLayer←-resp G σ ρ
            (value-trans (codeᵂ G) (substTargetEnv G σ ρ)
              (paraLayerFix-paraLayerC-out
                (substFix←-alg G σ ρ)
                (rollC targetLayer))
              (out-roll targetLayer)))
          (value-trans (codeᵂ (sub (extˢ σ) G)) (substSourceEnv G σ ρ)
            (substLayer-round←→ G σ ρ sourceLayer)
            (paraLayerFix-out children holes recursiveResults))))
      (roll-out {D = codeᵂ (sub (extˢ σ) G)} {ρ = ρ}
        (sup s children , holes))
    where
      recursiveResults :
        (p : Cont.Position (codeᵂ (sub (extˢ σ) G)) s zero) →
        Carrier (FixS (codeᵂ G) (substEnv σ ρ))
      recursiveResults p =
        substFix→-to G σ ρ
          (children p , λ i q → holes i (belowW p q))

      sourceLayer :
        Cont.Value (codeᵂ (sub (extˢ σ) G))
          (fixEnv (codeᵂ (sub (extˢ σ) G)) ρ)
      sourceLayer =
        paraLayerFix
          (paraLayerWith
            {D = codeᵂ (sub (extˢ σ) G)}
            {ρ = ρ}
            {A = Carrier (FixS (codeᵂ G) (substEnv σ ρ))}
            {s = s}
            children holes recursiveResults)

      targetLayer :
        Cont.Value (codeᵂ G)
          (fixEnv (codeᵂ G) (substEnv σ ρ))
      targetLayer = substLayer→ G σ ρ sourceLayer

  subst-round←→ : ∀ {n m} (T : Ty HO n) (σ : Sub HO n m) (ρ : Env m) →
    _≈⇒_ (subst←ᵉ T σ ρ ∘⇒ subst→ᵉ T σ ρ)
          (id⇒ {A = Semᵉ (sub σ T) ρ})
  subst-round←→ `𝟘 σ ρ ()
  subst-round←→ `𝟙 σ ρ x = tt
  subst-round←→ (T `× U) σ ρ (x , y) =
    subst-round←→ T σ ρ x , subst-round←→ U σ ρ y
  subst-round←→ (T `+ U) σ ρ (inj₁ x) =
    inj₁≈ (subst-round←→ T σ ρ x)
  subst-round←→ (T `+ U) σ ρ (inj₂ y) =
    inj₂≈ (subst-round←→ U σ ρ y)
  subst-round←→ (A `⇒ G) σ ρ f x =
    subst-round←→ G σ ρ (to f x)
  subst-round←→ (` i) σ ρ x = reflˢ (Semᵉ (σ i) ρ)
  subst-round←→ (ind G) σ ρ =
    substFix-round←→ G σ ρ

  weaken-round→←-helper : ∀ {m} (T : Ty HO m) (ρ : Env m) (X : Setoid₀)
    {S : Ty HO (Nat.suc m)} →
    (e : S ≡ sub wkSub T) →
    _≈⇒_
      ( Eq.subst
          (λ R → Semᵉ R (ext ρ X) ⟶ Semᵉ T ρ)
          (sym e)
          (subst→ᵉ T wkSub (ext ρ X))
        ∘⇒
        Eq.subst
          (λ R → Semᵉ T ρ ⟶ Semᵉ R (ext ρ X))
          (sym e)
          (subst←ᵉ T wkSub (ext ρ X))
      )
      (id⇒ {A = Semᵉ T ρ})
  weaken-round→←-helper T ρ X refl =
    subst-round→← T wkSub (ext ρ X)

  weaken-round→← : ∀ {m} (T : Ty HO m) (ρ : Env m) (X : Setoid₀) →
    _≈⇒_ (weaken→ᵉ T ρ X ∘⇒ weaken←ᵉ T ρ X)
          (id⇒ {A = Semᵉ T ρ})
  weaken-round→← T ρ X =
    weaken-round→←-helper T ρ X (ren≡sub-varSub suc T)

  substFixEnv-round→← : ∀ {n m} (G : Ty HO (Nat.suc n))
    (σ : Sub HO n m) (ρ : Env m) →
    EnvMapRound (substFixEnv← G σ ρ) (substFixEnv→ G σ ρ)
  substFixEnv-round→← G σ ρ zero =
    substFix-round→← G σ ρ
  substFixEnv-round→← G σ ρ (suc i) =
    weaken-round→← (σ i) ρ (FixS (codeᵂ (sub (extˢ σ) G)) ρ)

  substLayer→-resp : ∀ {n m} (G : Ty HO (Nat.suc n))
    (σ : Sub HO n m) (ρ : Env m)
    {layer layer′ : Cont.Value (codeᵂ (sub (extˢ σ) G))
      (fixEnv (codeᵂ (sub (extˢ σ) G)) ρ)} →
    ValueEq (codeᵂ (sub (extˢ σ) G)) (substSourceEnv G σ ρ) layer layer′ →
    ValueEq (codeᵂ G) (substTargetEnv G σ ρ)
      (substLayer→ G σ ρ layer)
      (substLayer→ G σ ρ layer′)
  substLayer→-resp G σ ρ layer≈ =
    packᵉ-resp G (substTargetEnv G σ ρ)
      (resp (mapᵉ G (substFixEnv→ G σ ρ))
        (resp (subst→ᵉ G (extˢ σ) (substSourceEnv G σ ρ))
          (unpackᵉ-resp (sub (extˢ σ) G) (substSourceEnv G σ ρ) layer≈)))

  substLayer-round→← : ∀ {n m} (G : Ty HO (Nat.suc n))
    (σ : Sub HO n m) (ρ : Env m)
    (layer : Cont.Value (codeᵂ G)
      (fixEnv (codeᵂ G) (substEnv σ ρ))) →
    ValueEq (codeᵂ G) (substTargetEnv G σ ρ)
      (substLayer→ G σ ρ (substLayer← G σ ρ layer))
      layer
  substLayer-round→← G σ ρ layer =
    value-trans (codeᵂ G) (substTargetEnv G σ ρ)
      (packᵉ-resp G (substTargetEnv G σ ρ) semantic-round)
      (pack-unpackᵉ G (substTargetEnv G σ ρ) layer)
    where
      source : Env _
      source = substSourceEnv G σ ρ

      target : Env _
      target = substTargetEnv G σ ρ

      unpacked : Carrier (Semᵉ G target)
      unpacked = unpackᵉ-to G target layer

      substituted : Carrier (Semᵉ (sub (extˢ σ) G) source)
      substituted =
        to (subst←ᵉ G (extˢ σ) source)
          (to (mapᵉ G (substFixEnv← G σ ρ)) unpacked)

      semantic-round : _≈_ (Semᵉ G target)
        ( to (mapᵉ G (substFixEnv→ G σ ρ))
          (to (subst→ᵉ G (extˢ σ) source)
            (unpackᵉ-to (sub (extˢ σ) G) source
              (packᵉ-to (sub (extˢ σ) G) source substituted)))
        )
        unpacked
      semantic-round =
        transˢ (Semᵉ G target)
          (resp (mapᵉ G (substFixEnv→ G σ ρ))
            (transˢ (Semᵉ G (substEnv (extˢ σ) source))
              (resp (subst→ᵉ G (extˢ σ) source)
                (unpack-packᵉ (sub (extˢ σ) G) source substituted))
              (subst-round→← G (extˢ σ) source
                (to (mapᵉ G (substFixEnv← G σ ρ)) unpacked))))
          (mapᵉ-round G
            (substFixEnv← G σ ρ)
            (substFixEnv→ G σ ρ)
            (substFixEnv-round→← G σ ρ)
            unpacked)

  substFix-round→← : ∀ {n m} (G : Ty HO (Nat.suc n))
    (σ : Sub HO n m) (ρ : Env m) →
    _≈⇒_ (substFix→ᵉ G σ ρ ∘⇒ substFix←ᵉ G σ ρ)
          (id⇒ {A = FixS (codeᵂ G) (substEnv σ ρ)})
  substFix-round→← G σ ρ (sup s children , holes) =
    transˢ (FixS (codeᵂ G) (substEnv σ ρ))
      (rollC-resp
        (value-trans (codeᵂ G) (substTargetEnv G σ ρ)
          (substLayer→-resp G σ ρ
            (value-trans (codeᵂ (sub (extˢ σ) G)) (substSourceEnv G σ ρ)
              (paraLayerFix-paraLayerC-out
                (substFix→-alg G σ ρ)
                (rollC sourceLayer))
              (out-roll sourceLayer)))
          (value-trans (codeᵂ G) (substTargetEnv G σ ρ)
            (substLayer-round→← G σ ρ targetLayer)
            (paraLayerFix-out children holes recursiveResults))))
      (roll-out {D = codeᵂ G} {ρ = substEnv σ ρ}
        (sup s children , holes))
    where
      recursiveResults :
        (p : Cont.Position (codeᵂ G) s zero) →
        Carrier (FixS (codeᵂ (sub (extˢ σ) G)) ρ)
      recursiveResults p =
        substFix←-to G σ ρ
          (children p , λ i q → holes i (belowW p q))

      targetLayer :
        Cont.Value (codeᵂ G)
          (fixEnv (codeᵂ G) (substEnv σ ρ))
      targetLayer =
        paraLayerFix
          (paraLayerWith
            {D = codeᵂ G}
            {ρ = substEnv σ ρ}
            {A = Carrier (FixS (codeᵂ (sub (extˢ σ) G)) ρ)}
            {s = s}
            children holes recursiveResults)

      sourceLayer :
        Cont.Value (codeᵂ (sub (extˢ σ) G))
          (fixEnv (codeᵂ (sub (extˢ σ) G)) ρ)
      sourceLayer = substLayer← G σ ρ targetLayer

  subst-round→← : ∀ {n m} (T : Ty HO n) (σ : Sub HO n m) (ρ : Env m) →
    _≈⇒_ (subst→ᵉ T σ ρ ∘⇒ subst←ᵉ T σ ρ)
          (id⇒ {A = Semᵉ T (substEnv σ ρ)})
  subst-round→← `𝟘 σ ρ ()
  subst-round→← `𝟙 σ ρ x = tt
  subst-round→← (T `× U) σ ρ (x , y) =
    subst-round→← T σ ρ x , subst-round→← U σ ρ y
  subst-round→← (T `+ U) σ ρ (inj₁ x) =
    inj₁≈ (subst-round→← T σ ρ x)
  subst-round→← (T `+ U) σ ρ (inj₂ y) =
    inj₂≈ (subst-round→← U σ ρ y)
  subst-round→← (A `⇒ G) σ ρ f x =
    subst-round→← G σ ρ (to f x)
  subst-round→← (` i) σ ρ x = reflˢ (Semᵉ (σ i) ρ)
  subst-round→← (ind G) σ ρ =
    substFix-round→← G σ ρ

strengthFixEq : ∀ {n} (D : Cont.Container (Nat.suc n)) (ρ : Env n) (A : Setoid₀)
  {x y : Carrier (FixS D ρ)} {a b : Carrier A} →
  _≈_ (FixS D ρ) x y →
  _≈_ A a b →
  _≈_ (FixS D (productEnv ρ A))
    (proj₁ x , λ i p → proj₂ x i p , a)
    (proj₁ y , λ i p → proj₂ y i p , b)
strengthFixEq D ρ A (sup≈ children≈ holes≈) a≈b =
  sup≈
    (λ p → strengthFixEq D ρ A (children≈ p) a≈b)
    (λ i p → holes≈ i p , a≈b)

strengthFix : ∀ {n} (D : Cont.Container (Nat.suc n)) (ρ : Env n) (A : Setoid₀) →
  (FixS D ρ ×S A) ⟶ FixS D (productEnv ρ A)
strengthFix D ρ A = record
  { to = λ x → proj₁ (proj₁ x) , λ i p → proj₂ (proj₁ x) i p , proj₂ x
  ; resp = λ p → strengthFixEq D ρ A (proj₁ p) (proj₂ p)
  }

strengthᵒ : ∀ {n} (G : Ty HO n) (ρ : Env n) (A : Setoid₀) →
  (Semᵉ G ρ ×S A) ⟶ Semᵉ G (productEnv ρ A)
strengthᵒ `𝟘 ρ A = record
  { to = λ ()
  ; resp = λ {}
  }
strengthᵒ `𝟙 ρ A = record
  { to = λ _ → tt
  ; resp = λ _ → tt
  }
strengthᵒ (G `× H) ρ A = record
  { to = λ x →
      to (strengthᵒ G ρ A) (proj₁ (proj₁ x) , proj₂ x) ,
      to (strengthᵒ H ρ A) (proj₂ (proj₁ x) , proj₂ x)
  ; resp = λ p →
      resp (strengthᵒ G ρ A) (proj₁ (proj₁ p) , proj₂ p) ,
      resp (strengthᵒ H ρ A) (proj₂ (proj₁ p) , proj₂ p)
  }
strengthᵒ (G `+ H) ρ A = record
  { to = λ { (inj₁ x , a) → inj₁ (to (strengthᵒ G ρ A) (x , a))
           ; (inj₂ y , a) → inj₂ (to (strengthᵒ H ρ A) (y , a))
           }
  ; resp = λ { (inj₁≈ p , q) → inj₁≈ (resp (strengthᵒ G ρ A) (p , q))
             ; (inj₂≈ p , q) → inj₂≈ (resp (strengthᵒ H ρ A) (p , q))
             }
  }
strengthᵒ (B `⇒ G) ρ A = record
  { to = λ x → record
      { to = λ b → to (strengthᵒ G ρ A) (to (proj₁ x) b , proj₂ x)
      ; resp = λ p → resp (strengthᵒ G ρ A) (resp (proj₁ x) p , reflˢ A)
      }
  ; resp = λ p b → resp (strengthᵒ G ρ A) (proj₁ p b , proj₂ p)
  }
strengthᵒ (` i) ρ A = id⇒
strengthᵒ (ind G) ρ A = strengthFix (codeᵂ G) ρ A

strengthᵒ-π₁ : ∀ {n} (G : Ty HO n) (ρ : Env n) (A : Setoid₀) →
  _≈⇒_
    (mapᵉ G (fstEnvMap ρ A) ∘⇒ strengthᵒ G ρ A)
    (record { to = proj₁ ; resp = proj₁ })
strengthᵒ-π₁ `𝟘 ρ A (() , a)
strengthᵒ-π₁ `𝟙 ρ A x = tt
strengthᵒ-π₁ (G `× H) ρ A (x , a) =
  strengthᵒ-π₁ G ρ A (proj₁ x , a) ,
  strengthᵒ-π₁ H ρ A (proj₂ x , a)
strengthᵒ-π₁ (G `+ H) ρ A (inj₁ x , a) =
  inj₁≈ (strengthᵒ-π₁ G ρ A (x , a))
strengthᵒ-π₁ (G `+ H) ρ A (inj₂ y , a) =
  inj₂≈ (strengthᵒ-π₁ H ρ A (y , a))
strengthᵒ-π₁ (B `⇒ G) ρ A (f , a) b =
  strengthᵒ-π₁ G ρ A (to f b , a)
strengthᵒ-π₁ (` i) ρ A x = reflˢ (ρ i)
strengthᵒ-π₁ (ind G) ρ A (x , a) = fix-refl (codeᵂ G) ρ

strengthᵒ-naturalˡ : ∀ {n} (G : Ty HO n) {ρ σ : Env n}
  (η : EnvMap ρ σ) (A : Setoid₀) →
  _≈⇒_
    (mapᵉ G (productEnvMap η A) ∘⇒ strengthᵒ G ρ A)
    (strengthᵒ G σ A ∘⇒ map×⇒ (mapᵉ G η) (id⇒ {A = A}))
strengthᵒ-naturalˡ `𝟘 η A (() , a)
strengthᵒ-naturalˡ `𝟙 η A x = tt
strengthᵒ-naturalˡ (G `× H) η A (x , a) =
  strengthᵒ-naturalˡ G η A (proj₁ x , a) ,
  strengthᵒ-naturalˡ H η A (proj₂ x , a)
strengthᵒ-naturalˡ (G `+ H) η A (inj₁ x , a) =
  inj₁≈ (strengthᵒ-naturalˡ G η A (x , a))
strengthᵒ-naturalˡ (G `+ H) η A (inj₂ y , a) =
  inj₂≈ (strengthᵒ-naturalˡ H η A (y , a))
strengthᵒ-naturalˡ (C `⇒ G) η A (f , a) c =
  strengthᵒ-naturalˡ G η A (to f c , a)
strengthᵒ-naturalˡ (` i) {σ = σ} η A (x , a) =
  reflˢ (σ i) , reflˢ A
strengthᵒ-naturalˡ (ind G) {σ = σ} η A (x , a) =
  valueFix→fixEq (codeᵂ G) (productEnv σ A)
    (value≈ λ i p → reflˢ (σ i) , reflˢ A)

strengthᵒ-naturalʳ : ∀ {n} (G : Ty HO n) (ρ : Env n)
  {A B : Setoid₀} (f : A ⟶ B) →
  _≈⇒_
    (mapᵉ G (sndEnvMap ρ f) ∘⇒ strengthᵒ G ρ A)
    (strengthᵒ G ρ B ∘⇒ map×⇒ (id⇒ {A = Semᵉ G ρ}) f)
strengthᵒ-naturalʳ `𝟘 ρ f (() , a)
strengthᵒ-naturalʳ `𝟙 ρ f x = tt
strengthᵒ-naturalʳ (G `× H) ρ f (x , a) =
  strengthᵒ-naturalʳ G ρ f (proj₁ x , a) ,
  strengthᵒ-naturalʳ H ρ f (proj₂ x , a)
strengthᵒ-naturalʳ (G `+ H) ρ f (inj₁ x , a) =
  inj₁≈ (strengthᵒ-naturalʳ G ρ f (x , a))
strengthᵒ-naturalʳ (G `+ H) ρ f (inj₂ y , a) =
  inj₂≈ (strengthᵒ-naturalʳ H ρ f (y , a))
strengthᵒ-naturalʳ (C `⇒ G) ρ f (g , a) c =
  strengthᵒ-naturalʳ G ρ f (to g c , a)
strengthᵒ-naturalʳ (` i) ρ {B = B} f (x , a) =
  reflˢ (ρ i) , reflˢ B
strengthᵒ-naturalʳ (ind G) ρ {B = B} f (x , a) =
  valueFix→fixEq (codeᵂ G) (productEnv ρ B)
    (value≈ λ i p → reflˢ (ρ i) , reflˢ B)

----------------------------------------------------------------------
-- Agda functions as extensional maps between propositional setoids
----------------------------------------------------------------------

PropSetoid : Set → Setoid₀
PropSetoid A = record
  { Carrier = A
  ; _≈_ = _≡_
  ; reflˢ = refl
  ; symˢ = sym
  ; transˢ = trans
  }

rawFunction : ∀ {A B : Set} → (A → B) → PropSetoid A ⟶ PropSetoid B
rawFunction f = record
  { to = f
  ; resp = cong f
  }

----------------------------------------------------------------------
-- PR-HO categorical structure
----------------------------------------------------------------------

Hom : TY HO → TY HO → Set
Hom T U = Sem T ⟶ Sem U

singleMap : ∀ {T U} → Hom T U →
  EnvMap (substEnv (σ₀ T) emptyEnv) (substEnv (σ₀ U) emptyEnv)
singleMap f zero = f

singleMap-comp : ∀ {A B D} (f : Hom B D) (g : Hom A B) →
  EnvMapComp
    (singleMap {T = A} {U = B} g)
    (singleMap {T = B} {U = D} f)
    (singleMap {T = A} {U = D} (f ∘⇒ g))
singleMap-comp {D = D} f g zero x = reflˢ (Sem D)

singleMap-id-round : ∀ {A} →
  EnvMapRound
    (singleMap {T = A} {U = A} (id⇒ {A = Sem A}))
    (singleMap {T = A} {U = A} (id⇒ {A = Sem A}))
singleMap-id-round {A} zero x = reflˢ (Sem A)

singleMap-id : ∀ {A} →
  EnvMapId (singleMap {T = A} {U = A} (id⇒ {A = Sem A}))
singleMap-id {A} zero x = reflˢ (Sem A)

strengthSubEnvMap : ∀ {T U} →
  EnvMap
    (productEnv (substEnv (σ₀ T) emptyEnv) (Sem U))
    (substEnv (σ₀ (T `× U)) emptyEnv)
strengthSubEnvMap zero = id⇒

strengthSubEnvMap-π₁-comp : ∀ {T U} →
  EnvMapComp
    (strengthSubEnvMap {T = T} {U = U})
    (singleMap {T = T `× U} {U = T} (record { to = proj₁ ; resp = proj₁ }))
    (fstEnvMap (substEnv (σ₀ T) emptyEnv) (Sem U))
strengthSubEnvMap-π₁-comp {T = T} zero x = reflˢ (Sem T)

strengthSubEnvMap-naturalʳ : ∀ {A B D} (g : Hom B D) →
  EnvMapEq
    (λ i →
      singleMap {T = A `× B} {U = A `× D}
        (map×⇒ (id⇒ {A = Sem A}) g) i
      ∘⇒ strengthSubEnvMap {T = A} {U = B} i)
    (λ i →
      strengthSubEnvMap {T = A} {U = D} i
      ∘⇒ sndEnvMap (substEnv (σ₀ A) emptyEnv) g i)
strengthSubEnvMap-naturalʳ {A = A} {D = D} g zero x =
  reflˢ (Sem A) , reflˢ (Sem D)

strengthSubEnvMap-naturalˡ : ∀ {A B D} (f : Hom A B) →
  EnvMapEq
    (compEnvMap
      (strengthSubEnvMap {T = A} {U = D})
      (singleMap {T = A `× D} {U = B `× D}
        (map×⇒ f (id⇒ {A = Sem D}))))
    (compEnvMap
      (productEnvMap (singleMap {T = A} {U = B} f) (Sem D))
      (strengthSubEnvMap {T = B} {U = D}))
strengthSubEnvMap-naturalˡ {B = B} {D = D} f zero x =
  reflˢ (Sem B) , reflˢ (Sem D)

terminal : ∀ {T} → Hom T `𝟙
terminal = record
  { to = λ _ → tt
  ; resp = λ _ → tt
  }

initial : ∀ {T} → Hom `𝟘 T
initial = record
  { to = λ ()
  ; resp = λ {}
  }

pair : ∀ {T U V} → Hom T U → Hom T V → Hom T (U `× V)
pair f g = record
  { to = λ x → to f x , to g x
  ; resp = λ p → resp f p , resp g p
  }

π₁ : ∀ {T U} → Hom (T `× U) T
π₁ = record
  { to = proj₁
  ; resp = proj₁
  }

π₂ : ∀ {T U} → Hom (T `× U) U
π₂ = record
  { to = proj₂
  ; resp = proj₂
  }

ι₁ : ∀ {T U} → Hom T (T `+ U)
ι₁ = record
  { to = inj₁
  ; resp = inj₁≈
  }

ι₂ : ∀ {T U} → Hom U (T `+ U)
ι₂ = record
  { to = inj₂
  ; resp = inj₂≈
  }

case : ∀ {T U V} → Hom T V → Hom U V → Hom (T `+ U) V
case f g = record
  { to = λ { (inj₁ x) → to f x ; (inj₂ y) → to g y }
  ; resp = λ { (inj₁≈ p) → resp f p ; (inj₂≈ p) → resp g p }
  }

lam : ∀ {T U V} → Hom (T `× U) V → Hom T (U `⇒ V)
lam {T = T} {U = U} {V = V} f = record
  { to = λ x → record
      { to = λ y → to f (x , y)
      ; resp = λ q → resp f (reflˢ (Sem T) , q)
      }
  ; resp = λ p y → resp f (p , reflˢ (Sem U))
  }

apply : ∀ {T U} → Hom ((T `⇒ U) `× T) U
apply {T = T} {U = U} = record
  { to = λ x → to (proj₁ x) (proj₂ x)
  ; resp = λ { {x = f , x} {y = g , y} (f≈g , x≈y) →
      transˢ (Sem U) (f≈g x) (resp g x≈y)
    }
  }

fmapᵉ : ∀ {T U} (G : Ty HO 1) → Hom T U → Hom (G [ T ]) (G [ U ])
fmapᵉ {T} {U} G f =
  subst←ᵉ G (σ₀ U) emptyEnv
  ∘⇒ mapᵉ G (singleMap f)
  ∘⇒ subst→ᵉ G (σ₀ T) emptyEnv

strengthᵉ : ∀ {T U} (G : Ty HO 1) → Hom ((G [ T ]) `× U) (G [ T `× U ])
strengthᵉ {T} {U} G =
  subst←ᵉ G (σ₀ (T `× U)) emptyEnv
  ∘⇒ mapᵉ G strengthSubEnvMap
  ∘⇒ strengthᵒ G (substEnv (σ₀ T) emptyEnv) (Sem U)
  ∘⇒ map×⇒ (subst→ᵉ G (σ₀ T) emptyEnv) (id⇒ {A = Sem U})

rollCon : ∀ {G : Ty HO 1} →
  ContainerS (codeᵂ G) (substEnv (σ₀ (ind G)) emptyEnv) ⟶ Sem (ind G)
rollCon {G} = record
  { to = λ { (s , values) →
      sup s (λ p → proj₁ (values zero p)) , λ ()
      }
  ; resp = λ { {x = s , xs} {y = .s , ys} (value≈ p) →
      sup≈
        (λ q →
          transˢ (Sem (ind G))
            (symˢ (Sem (ind G)) (forget-empty-holes (codeᵂ G) (xs zero q)))
            (transˢ (Sem (ind G)) (p zero q)
              (forget-empty-holes (codeᵂ G) (ys zero q))))
        (λ ())
      }
  }

conᵉ : ∀ {G : Ty HO 1} → Hom (G [ ind G ]) (ind G)
conᵉ {G} =
  rollCon {G = G}
  ∘⇒ packᵉ G (substEnv (σ₀ (ind G)) emptyEnv)
  ∘⇒ subst→ᵉ G (σ₀ (ind G)) emptyEnv

paraLayer→subst : ∀ {T : TY HO} {G : Ty HO 1} →
  Cont.Value (codeᵂ G) (paraEnv (codeᵂ G) emptyEnv (Carrier (Sem T))) →
  Cont.Value (codeᵂ G)
    (λ i → Carrier (substEnv (σ₀ (T `× ind G)) emptyEnv i))
paraLayer→subst (s , values) = s , λ { zero p → values zero p }

prAlgebra : ∀ {T U} {G : Ty HO 1} →
  Hom ((G [ T `× ind G ]) `× U) T →
  Carrier (Sem U) →
  Cont.Value (codeᵂ G) (paraEnv (codeᵂ G) emptyEnv (Carrier (Sem T))) →
  Carrier (Sem T)
prAlgebra {T} {U} {G} h u layer =
  to h
    ( to (subst←ᵉ G (σ₀ (T `× ind G)) emptyEnv)
        (unpackᵉ-to G (substEnv (σ₀ (T `× ind G)) emptyEnv)
          (paraLayer→subst layer))
    , u
    )

prAlgebra-resp : ∀ {T U} {G : Ty HO 1}
  (h : Hom ((G [ T `× ind G ]) `× U) T)
  {u v : Carrier (Sem U)} →
  _≈_ (Sem U) u v →
  {layer layer′ :
    Cont.Value (codeᵂ G) (paraEnv (codeᵂ G) emptyEnv (Carrier (Sem T)))} →
  ValueEq (codeᵂ G) (substEnv (σ₀ (T `× ind G)) emptyEnv)
    (paraLayer→subst layer) (paraLayer→subst layer′) →
  _≈_ (Sem T)
    (prAlgebra {T = T} {U = U} {G = G} h u layer)
    (prAlgebra {T = T} {U = U} {G = G} h v layer′)
prAlgebra-resp {T} {U} {G} h u≈v layer≈ =
  resp h
    ( resp (subst←ᵉ G (σ₀ (T `× ind G)) emptyEnv)
        (unpackᵉ-resp G (substEnv (σ₀ (T `× ind G)) emptyEnv) layer≈)
    , u≈v
    )

prAlgebra-cong : ∀ {T U} {G : Ty HO 1}
  {h h′ : Hom ((G [ T `× ind G ]) `× U) T} →
  _≈⇒_ {A = Sem ((G [ T `× ind G ]) `× U)} {B = Sem T} h h′ →
  (u : Carrier (Sem U)) →
  {layer layer′ :
    Cont.Value (codeᵂ G) (paraEnv (codeᵂ G) emptyEnv (Carrier (Sem T)))} →
  ValueEq (codeᵂ G) (substEnv (σ₀ (T `× ind G)) emptyEnv)
    (paraLayer→subst layer) (paraLayer→subst layer′) →
  _≈_ (Sem T)
    (prAlgebra {T = T} {U = U} {G = G} h u layer)
    (prAlgebra {T = T} {U = U} {G = G} h′ u layer′)
prAlgebra-cong {T} {U} {G} {h} {h′} h≈h′ u {layer} {layer′} layer≈ =
  transˢ (Sem T)
    (h≈h′
      ( to (subst←ᵉ G (σ₀ (T `× ind G)) emptyEnv)
          (unpackᵉ-to G (substEnv (σ₀ (T `× ind G)) emptyEnv)
            (paraLayer→subst layer))
      , u
      ))
    (resp h′
      ( resp (subst←ᵉ G (σ₀ (T `× ind G)) emptyEnv)
          (unpackᵉ-resp G (substEnv (σ₀ (T `× ind G)) emptyEnv) layer≈)
      , reflˢ (Sem U)
      ))

pr-resp : ∀ {T U} {G : Ty HO 1}
  (h : Hom ((G [ T `× ind G ]) `× U) T)
  {x y : Carrier (Sem (ind G))}
  {u v : Carrier (Sem U)} →
  _≈_ (Sem (ind G)) x y →
  _≈_ (Sem U) u v →
  _≈_ (Sem T)
    (paraC (prAlgebra {T = T} {U = U} {G = G} h u) x)
    (paraC (prAlgebra {T = T} {U = U} {G = G} h v) y)
pr-resp {T} {U} {G} h (sup≈ children≈ holes≈) u≈v =
  prAlgebra-resp {T = T} {U = U} {G = G} h u≈v
    (value≈ λ { zero p →
      pr-resp {T = T} {U = U} {G = G} h (children≈ p) u≈v ,
      children≈ p })

pr-cong-tree : ∀ {T U} {G : Ty HO 1}
  {h h′ : Hom ((G [ T `× ind G ]) `× U) T} →
  _≈⇒_ {A = Sem ((G [ T `× ind G ]) `× U)} {B = Sem T} h h′ →
  (u : Carrier (Sem U)) →
  (tree : W (codeᵂ G)) →
  (holes : ∀ i → WPos (codeᵂ G) tree i → Carrier (emptyEnv i)) →
  _≈_ (Sem T)
    (paraGo (prAlgebra {T = T} {U = U} {G = G} h u) tree holes)
    (paraGo (prAlgebra {T = T} {U = U} {G = G} h′ u) tree holes)
pr-cong-tree {T} {U} {G} {h} {h′} h≈h′ u (sup s children) holes =
  prAlgebra-cong {T = T} {U = U} {G = G} {h = h} {h′ = h′} h≈h′ u
    (value≈ λ { zero p →
      pr-cong-tree {T = T} {U = U} {G = G} {h = h} {h′ = h′}
        h≈h′ u (children p) (λ i q → holes i (belowW p q)) ,
      fix-refl (codeᵂ G) emptyEnv
      })

pr-cong : ∀ {T U} {G : Ty HO 1}
  {h h′ : Hom ((G [ T `× ind G ]) `× U) T} →
  _≈⇒_ {A = Sem ((G [ T `× ind G ]) `× U)} {B = Sem T} h h′ →
  (x : Carrier (Sem (ind G))) →
  (u : Carrier (Sem U)) →
  _≈_ (Sem T)
    (paraC (prAlgebra {T = T} {U = U} {G = G} h u) x)
    (paraC (prAlgebra {T = T} {U = U} {G = G} h′ u) x)
pr-cong {T} {U} {G} {h} {h′} h≈h′ (tree , holes) u =
  pr-cong-tree {T = T} {U = U} {G = G} {h = h} {h′ = h′} h≈h′ u tree holes

Prᵉ : ∀ {T U} {G : Ty HO 1} → Hom ((G [ T `× ind G ]) `× U) T → Hom (ind G `× U) T
Prᵉ {T} {U} {G} h = record
  { to = λ x → paraC (prAlgebra {T = T} {U = U} {G = G} h (proj₂ x)) (proj₁ x)
  ; resp = λ p → pr-resp {T = T} {U = U} {G = G} h (proj₁ p) (proj₂ p)
  }

prIndEnv : Ty HO 1 → Env 1
prIndEnv G = substEnv (σ₀ (ind G)) emptyEnv

prArgEnv : TY HO → Ty HO 1 → Env 1
prArgEnv A G = substEnv (σ₀ (A `× ind G)) emptyEnv

closedInd-normalize : ∀ {G : Ty HO 1} →
  (x : Carrier (Sem (ind G))) →
  _≈_ (Sem (ind G)) (proj₁ x , λ ()) x
closedInd-normalize {G} x =
  fix-sym (codeᵂ G) emptyEnv (forget-empty-holes (codeᵂ G) x)

paraChildᵉ : ∀ {A B} {G : Ty HO 1} →
  Hom ((G [ A `× ind G ]) `× B) A →
  Carrier (Sem B) →
  Carrier (Sem (ind G)) →
  Carrier (Sem (A `× ind G))
paraChildᵉ {A} {B} {G} h u x =
  to (Prᵉ {T = A} {U = B} {G = G} h) ((proj₁ x , λ ()) , u) ,
  (proj₁ x , λ ())

paraChild≈ᵉ : ∀ {A B} {G : Ty HO 1}
  (h : Hom ((G [ A `× ind G ]) `× B) A)
  (u : Carrier (Sem B))
  (x : Carrier (Sem (ind G))) →
  _≈_ (Sem (A `× ind G))
    (paraChildᵉ {A = A} {B = B} {G = G} h u x)
    (to (Prᵉ {T = A} {U = B} {G = G} h) (x , u) , x)
paraChild≈ᵉ {A = A} {B = B} {G = G} h u x =
  resp (Prᵉ {T = A} {U = B} {G = G} h)
    (closedInd-normalize {G = G} x , reflˢ (Sem B)) ,
  closedInd-normalize {G = G} x

paraEnvMapᵉ : ∀ {A B} {G : Ty HO 1} →
  Hom ((G [ A `× ind G ]) `× B) A →
  EnvMap (productEnv (prIndEnv G) (Sem B)) (prArgEnv A G)
paraEnvMapᵉ {A} {B} {G} h =
  compEnvMap
    (strengthSubEnvMap {T = ind G} {U = B})
    (singleMap {T = ind G `× B} {U = A `× ind G}
      (pair {T = ind G `× B} {U = A} {V = ind G}
        (Prᵉ {T = A} {U = B} {G = G} h)
        (π₁ {T = ind G} {U = B})))

paraLayerFromPackᵉ : ∀ {A B} {G : Ty HO 1} (F : Ty HO 1) →
  Hom ((G [ A `× ind G ]) `× B) A →
  Carrier (Sem B) →
  Carrier (Semᵉ F (prIndEnv G)) →
  Cont.Value (codeᵂ F) (λ i → Carrier (prArgEnv A G i))
paraLayerFromPackᵉ {A = A} {B = B} {G = G} F h u x
  with packᵉ-to F (prIndEnv G) x
... | s , values =
  s , λ { zero p → paraChildᵉ {A = A} {B = B} {G = G} h u (values zero p) }

paraLayerConᵉ : ∀ {A B} {G : Ty HO 1} →
  Hom ((G [ A `× ind G ]) `× B) A →
  Carrier (Sem B) →
  Carrier (Semᵉ G (prIndEnv G)) →
  Cont.Value (codeᵂ G) (λ i → Carrier (prArgEnv A G i))
paraLayerConᵉ {A} {B} {G} h u x
  with packᵉ-to G (prIndEnv G) x
... | s , values =
  paraLayer→subst {T = A} {G = G}
    (paraLayerWith
      {D = codeᵂ G}
      {ρ = emptyEnv}
      {A = Carrier (Sem A)}
      {s = s}
      (λ p → proj₁ (values zero p))
      (λ ())
      (λ p → paraGo (prAlgebra {T = A} {U = B} {G = G} h u)
        (proj₁ (values zero p)) (λ ())))

paraLayerCon-packᵉ : ∀ {A B} {G : Ty HO 1}
  (h : Hom ((G [ A `× ind G ]) `× B) A)
  (u : Carrier (Sem B))
  (x : Carrier (Semᵉ G (prIndEnv G))) →
  ValueEq (codeᵂ G) (prArgEnv A G)
    (paraLayerConᵉ {A = A} {B = B} {G = G} h u x)
    (paraLayerFromPackᵉ {A = A} {B = B} {G = G} G h u x)
paraLayerCon-packᵉ {A} {B} {G} h u x
  with packᵉ-to G (prIndEnv G) x
... | s , values =
  value≈ λ { zero p → reflˢ (prArgEnv A G zero) }

paraLayer-openᵉ : ∀ {A B} {G : Ty HO 1} (F : Ty HO 1)
  (h : Hom ((G [ A `× ind G ]) `× B) A)
  (u : Carrier (Sem B))
  (x : Carrier (Semᵉ F (prIndEnv G))) →
  _≈_ (Semᵉ F (prArgEnv A G))
    (unpackᵉ-to F (prArgEnv A G)
      (paraLayerFromPackᵉ {A = A} {B = B} {G = G} F h u x))
    (to (mapᵉ F (paraEnvMapᵉ {A = A} {B = B} {G = G} h))
      (to (strengthᵒ F (prIndEnv G) (Sem B)) (x , u)))
paraLayer-openᵉ `𝟘 h u ()
paraLayer-openᵉ `𝟙 h u tt = tt
paraLayer-openᵉ {A} {B} {G} (F `× H) h u (x , y)
  with packᵉ-to F (prIndEnv G) x
     | paraLayer-openᵉ {A = A} {B = B} {G = G} F h u x
     | packᵉ-to H (prIndEnv G) y
     | paraLayer-openᵉ {A = A} {B = B} {G = G} H h u y
... | sx , xs | px | sy , ys | py =
  transˢ (Semᵉ F (prArgEnv A G))
    (unpackᵉ-resp F (prArgEnv A G)
      (value≈ λ { zero p → reflˢ (prArgEnv A G zero) }))
    px ,
  transˢ (Semᵉ H (prArgEnv A G))
    (unpackᵉ-resp H (prArgEnv A G)
      (value≈ λ { zero p → reflˢ (prArgEnv A G zero) }))
    py
paraLayer-openᵉ {A} {B} {G} (F `+ H) h u (inj₁ x)
  with packᵉ-to F (prIndEnv G) x
     | paraLayer-openᵉ {A = A} {B = B} {G = G} F h u x
... | sx , xs | px =
  inj₁≈
    (transˢ (Semᵉ F (prArgEnv A G))
      (unpackᵉ-resp F (prArgEnv A G)
        (value≈ λ { zero p → reflˢ (prArgEnv A G zero) }))
      px)
paraLayer-openᵉ {A} {B} {G} (F `+ H) h u (inj₂ y)
  with packᵉ-to H (prIndEnv G) y
     | paraLayer-openᵉ {A = A} {B = B} {G = G} H h u y
... | sy , ys | py =
  inj₂≈
    (transˢ (Semᵉ H (prArgEnv A G))
      (unpackᵉ-resp H (prArgEnv A G)
        (value≈ λ { zero p → reflˢ (prArgEnv A G zero) }))
      py)
paraLayer-openᵉ {A} {B} {G} (C `⇒ F) h u f c
  rewrite pack-shape-closed C c =
  transˢ (Semᵉ F (prArgEnv A G))
    (unpackᵉ-resp F (prArgEnv A G)
      (value≈ λ { zero p → reflˢ (prArgEnv A G zero) }))
    (transˢ (Semᵉ F (prArgEnv A G))
      (paraLayer-openᵉ {A = A} {B = B} {G = G} F h u
        (to f (shape→closed C (closed→shape C c))))
      (resp (mapᵉ F (paraEnvMapᵉ {A = A} {B = B} {G = G} h))
        (resp (strengthᵒ F (prIndEnv G) (Sem B))
          (resp f (closed→shape→closed C c) , reflˢ (Sem B)))))
paraLayer-openᵉ {A} {B} {G} (` zero) h u x =
  paraChild≈ᵉ {A = A} {B = B} {G = G} h u x
paraLayer-openᵉ {A} {B} {G} (ind F) h u x =
  valueFix→fixEq (codeᵂ F) (prArgEnv A G)
    (value≈ λ { zero p → paraChild≈ᵉ {A = A} {B = B} {G = G} h u (proj₂ x zero p) })

paraChildᵖ : ∀ {A B} {G : Ty HO 1} →
  Hom (ind G `× B) A →
  Carrier (Sem B) →
  Carrier (Sem (ind G)) →
  Carrier (Sem (A `× ind G))
paraChildᵖ {A} {B} {G} p u x =
  to p ((proj₁ x , λ ()) , u) , (proj₁ x , λ ())

paraChildᵖ≈ : ∀ {A B} {G : Ty HO 1}
  (p : Hom (ind G `× B) A)
  (u : Carrier (Sem B))
  (x : Carrier (Sem (ind G))) →
  _≈_ (Sem (A `× ind G))
    (paraChildᵖ {A = A} {B = B} {G = G} p u x)
    (to p (x , u) , x)
paraChildᵖ≈ {B = B} {G = G} p u x =
  resp p (closedInd-normalize {G = G} x , reflˢ (Sem B)) ,
  closedInd-normalize {G = G} x

paraEnvMapᵖ : ∀ {A B} {G : Ty HO 1} →
  Hom (ind G `× B) A →
  EnvMap (productEnv (prIndEnv G) (Sem B)) (prArgEnv A G)
paraEnvMapᵖ {A} {B} {G} p =
  compEnvMap
    (strengthSubEnvMap {T = ind G} {U = B})
    (singleMap {T = ind G `× B} {U = A `× ind G}
      (pair {T = ind G `× B} {U = A} {V = ind G}
        p
        (π₁ {T = ind G} {U = B})))

paraLayerFromPackᵖ : ∀ {A B} {G : Ty HO 1} (F : Ty HO 1) →
  Hom (ind G `× B) A →
  Carrier (Sem B) →
  Carrier (Semᵉ F (prIndEnv G)) →
  Cont.Value (codeᵂ F) (λ i → Carrier (prArgEnv A G i))
paraLayerFromPackᵖ {A = A} {B = B} {G = G} F p u x
  with packᵉ-to F (prIndEnv G) x
... | s , values =
  s , λ { zero q → paraChildᵖ {A = A} {B = B} {G = G} p u (values zero q) }

paraLayer-openᵖ : ∀ {A B} {G : Ty HO 1} (F : Ty HO 1)
  (p : Hom (ind G `× B) A)
  (u : Carrier (Sem B))
  (x : Carrier (Semᵉ F (prIndEnv G))) →
  _≈_ (Semᵉ F (prArgEnv A G))
    (unpackᵉ-to F (prArgEnv A G)
      (paraLayerFromPackᵖ {A = A} {B = B} {G = G} F p u x))
    (to (mapᵉ F (paraEnvMapᵖ {A = A} {B = B} {G = G} p))
      (to (strengthᵒ F (prIndEnv G) (Sem B)) (x , u)))
paraLayer-openᵖ `𝟘 p u ()
paraLayer-openᵖ `𝟙 p u tt = tt
paraLayer-openᵖ {A} {B} {G} (F `× H) p u (x , y)
  with packᵉ-to F (prIndEnv G) x
     | paraLayer-openᵖ {A = A} {B = B} {G = G} F p u x
     | packᵉ-to H (prIndEnv G) y
     | paraLayer-openᵖ {A = A} {B = B} {G = G} H p u y
... | sx , xs | px | sy , ys | py =
  transˢ (Semᵉ F (prArgEnv A G))
    (unpackᵉ-resp F (prArgEnv A G)
      (value≈ λ { zero q → reflˢ (prArgEnv A G zero) }))
    px ,
  transˢ (Semᵉ H (prArgEnv A G))
    (unpackᵉ-resp H (prArgEnv A G)
      (value≈ λ { zero q → reflˢ (prArgEnv A G zero) }))
    py
paraLayer-openᵖ {A} {B} {G} (F `+ H) p u (inj₁ x)
  with packᵉ-to F (prIndEnv G) x
     | paraLayer-openᵖ {A = A} {B = B} {G = G} F p u x
... | sx , xs | px =
  inj₁≈
    (transˢ (Semᵉ F (prArgEnv A G))
      (unpackᵉ-resp F (prArgEnv A G)
        (value≈ λ { zero q → reflˢ (prArgEnv A G zero) }))
      px)
paraLayer-openᵖ {A} {B} {G} (F `+ H) p u (inj₂ y)
  with packᵉ-to H (prIndEnv G) y
     | paraLayer-openᵖ {A = A} {B = B} {G = G} H p u y
... | sy , ys | py =
  inj₂≈
    (transˢ (Semᵉ H (prArgEnv A G))
      (unpackᵉ-resp H (prArgEnv A G)
        (value≈ λ { zero q → reflˢ (prArgEnv A G zero) }))
      py)
paraLayer-openᵖ {A} {B} {G} (C `⇒ F) p u f c
  rewrite pack-shape-closed C c =
  transˢ (Semᵉ F (prArgEnv A G))
    (unpackᵉ-resp F (prArgEnv A G)
      (value≈ λ { zero q → reflˢ (prArgEnv A G zero) }))
    (transˢ (Semᵉ F (prArgEnv A G))
      (paraLayer-openᵖ {A = A} {B = B} {G = G} F p u
        (to f (shape→closed C (closed→shape C c))))
      (resp (mapᵉ F (paraEnvMapᵖ {A = A} {B = B} {G = G} p))
        (resp (strengthᵒ F (prIndEnv G) (Sem B))
          (resp f (closed→shape→closed C c) , reflˢ (Sem B)))))
paraLayer-openᵖ {A} {B} {G} (` zero) p u x =
  paraChildᵖ≈ {A = A} {B = B} {G = G} p u x
paraLayer-openᵖ {A} {B} {G} (ind F) p u x =
  valueFix→fixEq (codeᵂ F) (prArgEnv A G)
    (value≈ λ { zero q → paraChildᵖ≈ {A = A} {B = B} {G = G} p u (proj₂ x zero q) })

paraArgs-openᵖ : ∀ {A B} {G : Ty HO 1}
  (p : Hom (ind G `× B) A)
  (u : Carrier (Sem B))
  (x : Carrier (Semᵉ G (prIndEnv G))) →
  _≈_ (Sem (G [ A `× ind G ]))
    (to (subst←ᵉ G (σ₀ (A `× ind G)) emptyEnv)
      (unpackᵉ-to G (prArgEnv A G)
        (paraLayerFromPackᵖ {A = A} {B = B} {G = G} G p u x)))
    (to
      (fmapᵉ {T = ind G `× B} {U = A `× ind G} G
        (pair {T = ind G `× B} {U = A} {V = ind G}
          p
          (π₁ {T = ind G} {U = B}))
      ∘⇒ strengthᵉ {T = ind G} {U = B} G)
      (to (subst←ᵉ G (σ₀ (ind G)) emptyEnv) x , u))
paraArgs-openᵖ {A} {B} {G} p u x =
  resp (subst←ᵉ G (σ₀ (A `× ind G)) emptyEnv)
    (transˢ (Semᵉ G envAInd)
      (paraLayer-openᵖ {A = A} {B = B} {G = G} G p u x)
      (transˢ (Semᵉ G envAInd)
        (resp (mapᵉ G (paraEnvMapᵖ {A = A} {B = B} {G = G} p))
          (symˢ (Semᵉ G (productEnv envInd (Sem B)))
            (resp (strengthᵒ G envInd (Sem B))
              (subst-round→← G (σ₀ (ind G)) emptyEnv x , reflˢ (Sem B)))))
        (transˢ (Semᵉ G envAInd)
          (symˢ (Semᵉ G envAInd)
            (mapᵉ-comp G
              (strengthSubEnvMap {T = ind G} {U = B})
              mapPairSub
              (paraEnvMapᵖ {A = A} {B = B} {G = G} p)
              (compEnvMap-comp
                (strengthSubEnvMap {T = ind G} {U = B})
                mapPairSub)
              vClosed))
          (symˢ (Semᵉ G envAInd)
            (resp mapPair
              (subst-round→← G (σ₀ (ind G `× B)) emptyEnv wClosed))))))
  where
    envInd : Env 1
    envInd = prIndEnv G

    envAInd : Env 1
    envAInd = prArgEnv A G

    envIndB : Env 1
    envIndB = substEnv (σ₀ (ind G `× B)) emptyEnv

    yClosed : Carrier (Sem (G [ ind G ]))
    yClosed = to (subst←ᵉ G (σ₀ (ind G)) emptyEnv) x

    vClosed : Carrier (Semᵉ G (productEnv envInd (Sem B)))
    vClosed =
      to (strengthᵒ G envInd (Sem B))
        (to (subst→ᵉ G (σ₀ (ind G)) emptyEnv) yClosed , u)

    wClosed : Carrier (Semᵉ G envIndB)
    wClosed = to (mapᵉ G (strengthSubEnvMap {T = ind G} {U = B})) vClosed

    mapPairSub : EnvMap envIndB envAInd
    mapPairSub =
      singleMap {T = ind G `× B} {U = A `× ind G}
        (pair {T = ind G `× B} {U = A} {V = ind G}
          p
          (π₁ {T = ind G} {U = B}))

    mapPair : Semᵉ G envIndB ⟶ Semᵉ G envAInd
    mapPair = mapᵉ G mapPairSub

outClosedᵉ : ∀ {G : Ty HO 1} →
  Carrier (Sem (ind G)) →
  Cont.Value (codeᵂ G) (λ i → Carrier (prIndEnv G i))
outClosedᵉ (sup s children , holes) =
  s , λ { zero p → children p , λ () }

con-outᵉ : ∀ {G : Ty HO 1} (x : Carrier (Sem (ind G))) →
  _≈_ (Sem (ind G))
    (to (conᵉ {G = G})
      (to (subst←ᵉ G (σ₀ (ind G)) emptyEnv)
        (unpackᵉ-to G (prIndEnv G) (outClosedᵉ {G = G} x))))
    x
con-outᵉ {G} (sup s children , holes) =
  transˢ (Sem (ind G))
    (resp (rollCon {G = G})
      (value-trans (codeᵂ G) (prIndEnv G)
        (packᵉ-resp G (prIndEnv G)
          (subst-round→← G (σ₀ (ind G)) emptyEnv yOpen))
        (pack-unpackᵉ G (prIndEnv G) layer)))
    (fix-sym (codeᵂ G) emptyEnv
      (forget-empty-holes (codeᵂ G) (sup s children , holes)))
  where
    layer : Cont.Value (codeᵂ G) (λ i → Carrier (prIndEnv G i))
    layer = outClosedᵉ {G = G} (sup s children , holes)

    yOpen : Carrier (Semᵉ G (prIndEnv G))
    yOpen = unpackᵉ-to G (prIndEnv G) layer

paraLayerFromPack-Prᵉ : ∀ {A B} {G : Ty HO 1}
  (h : Hom ((G [ A `× ind G ]) `× B) A)
  (p : Hom (ind G `× B) A)
  (u : Carrier (Sem B))
  (x : Carrier (Semᵉ G (prIndEnv G))) →
  ((z : Carrier (Sem (ind G))) →
    _≈_ (Sem A)
      (to p ((proj₁ z , λ ()) , u))
      (to (Prᵉ {T = A} {U = B} {G = G} h) ((proj₁ z , λ ()) , u))) →
  ValueEq (codeᵂ G) (prArgEnv A G)
    (paraLayerFromPackᵖ {A = A} {B = B} {G = G} G p u x)
    (paraLayerFromPackᵉ {A = A} {B = B} {G = G} G h u x)
paraLayerFromPack-Prᵉ {A} {B} {G} h p u x child≈
  with packᵉ-to G (prIndEnv G) x
... | s , values =
  value≈ λ { zero q →
    child≈ (values zero q) , reflˢ (Sem (ind G)) }

paraLayerCon-outᵉ : ∀ {A B} {G : Ty HO 1}
  (h : Hom ((G [ A `× ind G ]) `× B) A)
  (u : Carrier (Sem B))
  (x : Carrier (Sem (ind G))) →
  ValueEq (codeᵂ G) (prArgEnv A G)
    (paraLayerConᵉ {A = A} {B = B} {G = G} h u
      (unpackᵉ-to G (prIndEnv G) (outClosedᵉ {G = G} x)))
    (paraLayer→subst {T = A} {G = G}
      (paraLayerC {D = codeᵂ G} {ρ = emptyEnv} {A = Carrier (Sem A)}
        (prAlgebra {T = A} {U = B} {G = G} h u)
        x))
paraLayerCon-outᵉ {A} {B} {G} h u (sup s children , holes)
  with packᵉ-to G (prIndEnv G)
        (unpackᵉ-to G (prIndEnv G)
          (outClosedᵉ {G = G} (sup s children , holes)))
     | pack-unpackᵉ G (prIndEnv G)
        (outClosedᵉ {G = G} (sup s children , holes))
... | .s , values | value≈ pointwise =
  value≈ λ { zero q →
    let child≈ =
          transˢ (Sem (ind G))
            (closedInd-normalize {G = G} (values zero q))
            (transˢ (Sem (ind G))
              (pointwise zero q)
              (fix-sym (codeᵂ G) emptyEnv
                (forget-empty-holes (codeᵂ G)
                  (children q , λ i r → holes i (belowW q r)))))
    in
    pr-resp {T = A} {U = B} {G = G} h child≈ (reflˢ (Sem B)) ,
    child≈ }

structure : PRHO.Structure Level.zero
structure = record
  { _⇒ᴹ_ = Hom
  ; idᴹ = λ {T} → id⇒ {A = Sem T}
  ; Cᴹ = λ f g → f ∘⇒ g
  ; ⊤ᴹ = λ {T} → terminal {T = T}
  ; ⊥ᴹ = λ {T} → initial {T = T}
  ; pairᴹ = λ {T} {U} {V} f g → pair {T = T} {U = U} {V = V} f g
  ; π₁ᴹ = λ {T} {U} → π₁ {T = T} {U = U}
  ; π₂ᴹ = λ {T} {U} → π₂ {T = T} {U = U}
  ; ι₁ᴹ = λ {T} {U} → ι₁ {T = T} {U = U}
  ; ι₂ᴹ = λ {T} {U} → ι₂ {T = T} {U = U}
  ; caseᴹ = λ {T} {U} {V} f g → case {T = T} {U = U} {V = V} f g
  ; lamᴹ = λ {T} {U} {V} f → lam {T = T} {U = U} {V = V} f
  ; applyᴹ = λ {T} {U} → apply {T = T} {U = U}
  ; fmapᴹ = λ {T} {U} G f → fmapᵉ {T = T} {U = U} G f
  ; strengthᴹ = λ {T} {U} G → strengthᵉ {T = T} {U = U} G
  ; conᴹ = λ {G} → conᵉ {G = G}
  ; Prᴹ = λ {T} {U} {G} h → Prᵉ {T = T} {U = U} {G = G} h
  }

infix 4 _≈ᴴ_

_≈ᴴ_ : ∀ {T U} → Hom T U → Hom T U → Set
_≈ᴴ_ {T} {U} = _≈⇒_ {A = Sem T} {B = Sem U}

map×ᴹᵉ : ∀ {T U V W} → Hom U T → Hom V W → Hom (U `× V) (T `× W)
map×ᴹᵉ {T = T} {U = U} {V = V} {W = W} =
  PRHO.map-×ᴹ structure {T = T} {U = U} {V = V} {W = W}

fmapᶜᵉ : ∀ {T U G} → StructuralFunctor G → Hom T U → Hom (G [ T ]) (G [ U ])
fmapᶜᵉ {T = T} {U = U} {G = G} =
  PRHO.fmapᶜᴹ structure {T = T} {U = U} {G = G}

strengthᶜᵉ : ∀ {T U G} → StructuralFunctor G → Hom ((G [ T ]) `× U) (G [ T `× U ])
strengthᶜᵉ {T = T} {U = U} {G = G} =
  PRHO.strengthᶜᴹ structure {T = T} {U = U} {G = G}

paraArgsᵉ : ∀ {T U} (G : Ty HO 1) →
  Hom (ind G `× U) T →
  Hom ((G [ ind G ]) `× U) ((G [ T `× ind G ]) `× U)
paraArgsᵉ {T = T} {U = U} G =
  PRHO.paraArgsᴹ structure {T = T} {U = U} G

fmap-congᵉ : ∀ {A B} (G : Ty HO 1) {f f′ : Hom A B} →
  _≈ᴴ_ {T = A} {U = B} f f′ →
  _≈ᴴ_ {T = G [ A ]} {U = G [ B ]}
    (fmapᵉ {T = A} {U = B} G f)
    (fmapᵉ {T = A} {U = B} G f′)
fmap-congᵉ {A} {B} G {f} {f′} f≈f′ x =
  resp (subst←ᵉ G (σ₀ B) emptyEnv)
    (mapᵉ-cong G {η = singleMap f} {θ = singleMap f′}
      (λ { zero → f≈f′ })
      (to (subst→ᵉ G (σ₀ A) emptyEnv) x))

Pr-congᵉ : ∀ {A B} {G : Ty HO 1}
  {h h′ : Hom ((G [ A `× ind G ]) `× B) A} →
  _≈ᴴ_ {T = (G [ A `× ind G ]) `× B} {U = A} h h′ →
  _≈ᴴ_ {T = ind G `× B} {U = A}
    (Prᵉ {T = A} {U = B} {G = G} h)
    (Prᵉ {T = A} {U = B} {G = G} h′)
Pr-congᵉ {A} {B} {G} {h} {h′} h≈h′ (x , u) =
  pr-cong {T = A} {U = B} {G = G} {h = h} {h′ = h′} h≈h′ x u

{-# TERMINATING #-}
substFix-fmap-idᵉ : ∀ {A} (G : Ty HO 2) →
  _≈ᴴ_ {T = ind G [ A ]} {U = ind G [ A ]}
    (fmapᵉ {T = A} {U = A} (ind G) (id⇒ {A = Sem A}))
    (id⇒ {A = Sem (ind G [ A ])})
substFix-fmap-idᵉ {A} G x =
  transˢ (Sem (ind G [ A ]))
    (resp (substFix←ᵉ G (σ₀ A) emptyEnv)
      (mapᵉ-id (ind G)
        {ρ = substEnv (σ₀ A) emptyEnv}
        (singleMap {T = A} {U = A} (id⇒ {A = Sem A}))
        (singleMap-id {A = A})
        (to (substFix→ᵉ G (σ₀ A) emptyEnv) x)))
    (substFix-round←→ G (σ₀ A) emptyEnv x)

fmap-idᵉ : ∀ {A} (G : Ty HO 1) →
  _≈ᴴ_ {T = G [ A ]} {U = G [ A ]}
    (fmapᵉ {T = A} {U = A} G (id⇒ {A = Sem A}))
    (id⇒ {A = Sem (G [ A ])})
fmap-idᵉ `𝟘 ()
fmap-idᵉ `𝟙 x = tt
fmap-idᵉ (G `× H) (x , y) =
  fmap-idᵉ G x , fmap-idᵉ H y
fmap-idᵉ (G `+ H) (inj₁ x) =
  inj₁≈ (fmap-idᵉ G x)
fmap-idᵉ (G `+ H) (inj₂ y) =
  inj₂≈ (fmap-idᵉ H y)
fmap-idᵉ (A `⇒ G) f x =
  fmap-idᵉ G (to f x)
fmap-idᵉ {A} (` zero) x = reflˢ (Sem A)
fmap-idᵉ (ind G) =
  substFix-fmap-idᵉ G

fmap-Cᵉ : ∀ {A B D} (G : Ty HO 1) {f : Hom B D} {g : Hom A B} →
  _≈ᴴ_ {T = G [ A ]} {U = G [ D ]}
    (fmapᵉ {T = A} {U = D} G (f ∘⇒ g))
    (fmapᵉ {T = B} {U = D} G f ∘⇒ fmapᵉ {T = A} {U = B} G g)
fmap-Cᵉ {A} {B} {D} G {f} {g} x =
  resp (subst←ᵉ G (σ₀ D) emptyEnv)
    (transˢ (Semᵉ G envD)
      (symˢ (Semᵉ G envD)
        (mapᵉ-comp G
          (singleMap {T = A} {U = B} g)
          (singleMap {T = B} {U = D} f)
          (singleMap {T = A} {U = D} (f ∘⇒ g))
          (singleMap-comp f g)
          z))
      (resp (mapᵉ G (singleMap {T = B} {U = D} f))
        (symˢ (Semᵉ G envB)
          (subst-round→← G (σ₀ B) emptyEnv y))))
  where
    envB : Env 1
    envB = substEnv (σ₀ B) emptyEnv

    envD : Env 1
    envD = substEnv (σ₀ D) emptyEnv

    z : Carrier (Semᵉ G (substEnv (σ₀ A) emptyEnv))
    z = to (subst→ᵉ G (σ₀ A) emptyEnv) x

    y : Carrier (Semᵉ G envB)
    y = to (mapᵉ G (singleMap {T = A} {U = B} g)) z

fmap-βᶜᵉ : ∀ {A B} {G : Ty HO 1} (S : StructuralFunctor G) {f : Hom A B} →
  _≈ᴴ_ {T = G [ A ]} {U = G [ B ]}
    (fmapᵉ {T = A} {U = B} G f)
    (fmapᶜᵉ {T = A} {U = B} {G = G} S f)
fmap-βᶜᵉ sf-𝟘 ()
fmap-βᶜᵉ sf-𝟙 x = tt
fmap-βᶜᵉ {B = B} sf-var x = reflˢ (Sem B)
fmap-βᶜᵉ (sf-× S R) (x , y) =
  fmap-βᶜᵉ S x , fmap-βᶜᵉ R y
fmap-βᶜᵉ (sf-+ S R) (inj₁ x) =
  inj₁≈ (fmap-βᶜᵉ S x)
fmap-βᶜᵉ (sf-+ S R) (inj₂ y) =
  inj₂≈ (fmap-βᶜᵉ R y)
fmap-βᶜᵉ (sf-⇒ A S) h x =
  fmap-βᶜᵉ S (to h x)

strength-π₁ᵉ : ∀ {A B} (G : Ty HO 1) →
  _≈ᴴ_ {T = (G [ A ]) `× B} {U = G [ A ]}
    (fmapᵉ {T = A `× B} {U = A} G (π₁ {T = A} {U = B})
      ∘⇒ strengthᵉ {T = A} {U = B} G)
    (π₁ {T = G [ A ]} {U = B})
strength-π₁ᵉ {A} {B} G x =
  transˢ (Sem (G [ A ]))
    (resp (subst←ᵉ G (σ₀ A) emptyEnv)
      (transˢ (Semᵉ G envA)
        (resp mapπ₁
          (subst-round→← G (σ₀ (A `× B)) emptyEnv w))
        (transˢ (Semᵉ G envA)
          (mapᵉ-comp G
            (strengthSubEnvMap {T = A} {U = B})
            (singleMap {T = A `× B} {U = A} (π₁ {T = A} {U = B}))
            (fstEnvMap envA (Sem B))
            (strengthSubEnvMap-π₁-comp {T = A} {U = B})
            v)
          (strengthᵒ-π₁ G envA (Sem B) strengthenedInput))))
    (subst-round←→ G (σ₀ A) emptyEnv (proj₁ x))
  where
    envA : Env 1
    envA = substEnv (σ₀ A) emptyEnv

    envAB : Env 1
    envAB = substEnv (σ₀ (A `× B)) emptyEnv

    mapπ₁ : Semᵉ G envAB ⟶ Semᵉ G envA
    mapπ₁ = mapᵉ G (singleMap {T = A `× B} {U = A} (π₁ {T = A} {U = B}))

    strengthenedInput : Carrier (Semᵉ G envA ×S Sem B)
    strengthenedInput =
      to (map×⇒ (subst→ᵉ G (σ₀ A) emptyEnv) (id⇒ {A = Sem B})) x

    v : Carrier (Semᵉ G (productEnv envA (Sem B)))
    v = to (strengthᵒ G envA (Sem B)) strengthenedInput

    w : Carrier (Semᵉ G envAB)
    w = to (mapᵉ G (strengthSubEnvMap {T = A} {U = B})) v

strength-βᶜᵉ : ∀ {A B} {G : Ty HO 1} (S : StructuralFunctor G) →
  _≈ᴴ_ {T = (G [ A ]) `× B} {U = G [ A `× B ]}
    (strengthᵉ {T = A} {U = B} G)
    (strengthᶜᵉ {T = A} {U = B} {G = G} S)
strength-βᶜᵉ sf-𝟘 (() , b)
strength-βᶜᵉ sf-𝟙 x = tt
strength-βᶜᵉ {A} {B} sf-var x = reflˢ (Sem (A `× B))
strength-βᶜᵉ (sf-× S R) ((x , y) , b) =
  strength-βᶜᵉ S (x , b) ,
  strength-βᶜᵉ R (y , b)
strength-βᶜᵉ (sf-+ S R) (inj₁ x , b) =
  inj₁≈ (strength-βᶜᵉ S (x , b))
strength-βᶜᵉ (sf-+ S R) (inj₂ y , b) =
  inj₂≈ (strength-βᶜᵉ R (y , b))
strength-βᶜᵉ (sf-⇒ C S) (f , b) c =
  strength-βᶜᵉ S (to f c , b)

strength-naturalˡᵉ : ∀ {A B D} (G : Ty HO 1) {f : Hom A B} →
  _≈ᴴ_ {T = (G [ A ]) `× D} {U = G [ B `× D ]}
  (fmapᵉ {T = A `× D} {U = B `× D} G
    (map×ᴹᵉ {T = B} {U = A} {V = D} {W = D} f (id⇒ {A = Sem D}))
    ∘⇒ strengthᵉ {T = A} {U = D} G)
  (strengthᵉ {T = B} {U = D} G
    ∘⇒ map×ᴹᵉ {T = G [ B ]} {U = G [ A ]} {V = D} {W = D}
          (fmapᵉ {T = A} {U = B} G f) (id⇒ {A = Sem D}))
strength-naturalˡᵉ {A} {B} {D} G {f} x =
  resp (subst←ᵉ G (σ₀ (B `× D)) emptyEnv)
    (transˢ (Semᵉ G envBD)
      (resp mapLeft
        (subst-round→← G (σ₀ (A `× D)) emptyEnv wAD))
      (transˢ (Semᵉ G envBD)
        (mapᵉ-comp G
          (strengthSubEnvMap {T = A} {U = D})
          mapLeftSub
          leftComp
          (compEnvMap-comp (strengthSubEnvMap {T = A} {U = D}) mapLeftSub)
          vAD)
        (transˢ (Semᵉ G envBD)
          (mapᵉ-cong G {η = leftComp} {θ = rightComp}
            (strengthSubEnvMap-naturalˡ {A = A} {B = B} {D = D} f)
            vAD)
          (transˢ (Semᵉ G envBD)
            (symˢ (Semᵉ G envBD)
              (mapᵉ-comp G
                productLeft
                (strengthSubEnvMap {T = B} {U = D})
                rightComp
                (compEnvMap-comp productLeft
                  (strengthSubEnvMap {T = B} {U = D}))
                vAD))
            (transˢ (Semᵉ G envBD)
              (resp (mapᵉ G (strengthSubEnvMap {T = B} {U = D}))
                (strengthᵒ-naturalˡ G {ρ = envA} {σ = envB}
                  singleF (Sem D) strengthenedInput))
              (resp (mapᵉ G (strengthSubEnvMap {T = B} {U = D}))
                (resp (strengthᵒ G envB (Sem D))
                  ( symˢ (Semᵉ G envB)
                      (subst-round→← G (σ₀ B) emptyEnv yB)
                  , reflˢ (Sem D)))))))))
  where
    envA : Env 1
    envA = substEnv (σ₀ A) emptyEnv

    envB : Env 1
    envB = substEnv (σ₀ B) emptyEnv

    envAD : Env 1
    envAD = substEnv (σ₀ (A `× D)) emptyEnv

    envBD : Env 1
    envBD = substEnv (σ₀ (B `× D)) emptyEnv

    singleF : EnvMap envA envB
    singleF = singleMap {T = A} {U = B} f

    productLeft : EnvMap (productEnv envA (Sem D)) (productEnv envB (Sem D))
    productLeft = productEnvMap singleF (Sem D)

    mapLeftSub : EnvMap envAD envBD
    mapLeftSub =
      singleMap {T = A `× D} {U = B `× D}
        (map×⇒ f (id⇒ {A = Sem D}))

    mapLeft : Semᵉ G envAD ⟶ Semᵉ G envBD
    mapLeft = mapᵉ G mapLeftSub

    leftComp : EnvMap (productEnv envA (Sem D)) envBD
    leftComp =
      compEnvMap (strengthSubEnvMap {T = A} {U = D}) mapLeftSub

    rightComp : EnvMap (productEnv envA (Sem D)) envBD
    rightComp =
      compEnvMap productLeft (strengthSubEnvMap {T = B} {U = D})

    strengthenedInput : Carrier (Semᵉ G envA ×S Sem D)
    strengthenedInput =
      to (map×⇒ (subst→ᵉ G (σ₀ A) emptyEnv) (id⇒ {A = Sem D})) x

    yB : Carrier (Semᵉ G envB)
    yB = to (mapᵉ G singleF) (proj₁ strengthenedInput)

    vAD : Carrier (Semᵉ G (productEnv envA (Sem D)))
    vAD = to (strengthᵒ G envA (Sem D)) strengthenedInput

    wAD : Carrier (Semᵉ G envAD)
    wAD = to (mapᵉ G (strengthSubEnvMap {T = A} {U = D})) vAD

strength-naturalʳᵉ : ∀ {A B D} (G : Ty HO 1) {g : Hom B D} →
  _≈ᴴ_ {T = (G [ A ]) `× B} {U = G [ A `× D ]}
  (fmapᵉ {T = A `× B} {U = A `× D} G
    (map×ᴹᵉ {T = A} {U = A} {V = B} {W = D} (id⇒ {A = Sem A}) g)
    ∘⇒ strengthᵉ {T = A} {U = B} G)
  (strengthᵉ {T = A} {U = D} G
    ∘⇒ map×ᴹᵉ {T = G [ A ]} {U = G [ A ]} {V = B} {W = D}
          (id⇒ {A = Sem (G [ A ])}) g)
strength-naturalʳᵉ {A} {B} {D} G {g} x =
  resp (subst←ᵉ G (σ₀ (A `× D)) emptyEnv)
    (transˢ (Semᵉ G envAD)
      (resp mapRight
        (subst-round→← G (σ₀ (A `× B)) emptyEnv wB))
      (transˢ (Semᵉ G envAD)
        (mapᵉ-comp G
          (strengthSubEnvMap {T = A} {U = B})
          mapRightSub
          leftComp
          (compEnvMap-comp (strengthSubEnvMap {T = A} {U = B}) mapRightSub)
          vB)
        (transˢ (Semᵉ G envAD)
          (mapᵉ-cong G {η = leftComp} {θ = rightComp}
            (strengthSubEnvMap-naturalʳ {A = A} {B = B} {D = D} g)
            vB)
          (transˢ (Semᵉ G envAD)
            (symˢ (Semᵉ G envAD)
              (mapᵉ-comp G
                (sndEnvMap envA g)
                (strengthSubEnvMap {T = A} {U = D})
                rightComp
                (compEnvMap-comp (sndEnvMap envA g)
                  (strengthSubEnvMap {T = A} {U = D}))
                vB))
            (resp (mapᵉ G (strengthSubEnvMap {T = A} {U = D}))
              (strengthᵒ-naturalʳ G envA g strengthenedInput))))))
  where
    envA : Env 1
    envA = substEnv (σ₀ A) emptyEnv

    envAB : Env 1
    envAB = substEnv (σ₀ (A `× B)) emptyEnv

    envAD : Env 1
    envAD = substEnv (σ₀ (A `× D)) emptyEnv

    mapRightSub : EnvMap envAB envAD
    mapRightSub =
      singleMap {T = A `× B} {U = A `× D}
        (map×⇒ (id⇒ {A = Sem A}) g)

    mapRight : Semᵉ G envAB ⟶ Semᵉ G envAD
    mapRight = mapᵉ G mapRightSub

    leftComp : EnvMap (productEnv envA (Sem B)) envAD
    leftComp =
      compEnvMap (strengthSubEnvMap {T = A} {U = B}) mapRightSub

    rightComp : EnvMap (productEnv envA (Sem B)) envAD
    rightComp =
      compEnvMap (sndEnvMap envA g) (strengthSubEnvMap {T = A} {U = D})

    strengthenedInput : Carrier (Semᵉ G envA ×S Sem B)
    strengthenedInput =
      to (map×⇒ (subst→ᵉ G (σ₀ A) emptyEnv) (id⇒ {A = Sem B})) x

    vB : Carrier (Semᵉ G (productEnv envA (Sem B)))
    vB = to (strengthᵒ G envA (Sem B)) strengthenedInput

    wB : Carrier (Semᵉ G envAB)
    wB = to (mapᵉ G (strengthSubEnvMap {T = A} {U = B})) vB

Pr-βᵉ : ∀ {A B} {G : Ty HO 1}
  {h : Hom ((G [ A `× ind G ]) `× B) A} →
  _≈ᴴ_ {T = (G [ ind G ]) `× B} {U = A}
  (Prᵉ {T = A} {U = B} {G = G} h
    ∘⇒ map×ᴹᵉ {T = ind G} {U = G [ ind G ]} {V = B} {W = B}
          (conᵉ {G = G}) (id⇒ {A = Sem B}))
  (h ∘⇒ paraArgsᵉ {T = A} {U = B} G (Prᵉ {T = A} {U = B} {G = G} h))
Pr-βᵉ {A} {B} {G} {h} x =
  resp h
    ( resp (subst←ᵉ G (σ₀ (A `× ind G)) emptyEnv)
        (transˢ (Semᵉ G envAInd)
          (unpackᵉ-resp G envAInd
            (paraLayerCon-packᵉ {A = A} {B = B} {G = G} h u yOpen))
          (transˢ (Semᵉ G envAInd)
            (paraLayer-openᵉ {A = A} {B = B} {G = G} G h u yOpen)
            (transˢ (Semᵉ G envAInd)
              (symˢ (Semᵉ G envAInd)
                (mapᵉ-comp G
                  (strengthSubEnvMap {T = ind G} {U = B})
                  mapPairSub
                  (paraEnvMapᵉ {A = A} {B = B} {G = G} h)
                  (compEnvMap-comp
                    (strengthSubEnvMap {T = ind G} {U = B})
                    mapPairSub)
                  v))
              (symˢ (Semᵉ G envAInd)
                (resp mapPair
                  (subst-round→← G (σ₀ (ind G `× B)) emptyEnv w))))))
    , reflˢ (Sem B))
  where
    envInd : Env 1
    envInd = prIndEnv G

    envAInd : Env 1
    envAInd = prArgEnv A G

    envIndB : Env 1
    envIndB = substEnv (σ₀ (ind G `× B)) emptyEnv

    y : Carrier (Sem (G [ ind G ]))
    y = proj₁ x

    u : Carrier (Sem B)
    u = proj₂ x

    yOpen : Carrier (Semᵉ G envInd)
    yOpen = to (subst→ᵉ G (σ₀ (ind G)) emptyEnv) y

    v : Carrier (Semᵉ G (productEnv envInd (Sem B)))
    v = to (strengthᵒ G envInd (Sem B)) (yOpen , u)

    w : Carrier (Semᵉ G envIndB)
    w = to (mapᵉ G (strengthSubEnvMap {T = ind G} {U = B})) v

    mapPairSub : EnvMap envIndB envAInd
    mapPairSub =
      singleMap {T = ind G `× B} {U = A `× ind G}
        (pair {T = ind G `× B} {U = A} {V = ind G}
          (Prᵉ {T = A} {U = B} {G = G} h)
          (π₁ {T = ind G} {U = B}))

    mapPair : Semᵉ G envIndB ⟶ Semᵉ G envAInd
    mapPair = mapᵉ G mapPairSub

pr-unique-treeᵉ : ∀ {A B} {G : Ty HO 1}
  {h : Hom ((G [ A `× ind G ]) `× B) A}
  {p : Hom (ind G `× B) A} →
  _≈ᴴ_ {T = (G [ ind G ]) `× B} {U = A}
    (p ∘⇒ map×ᴹᵉ {T = ind G} {U = G [ ind G ]} {V = B} {W = B}
          (conᵉ {G = G}) (id⇒ {A = Sem B}))
    (h ∘⇒ paraArgsᵉ {T = A} {U = B} G p) →
  (u : Carrier (Sem B)) →
  (tree : W (codeᵂ G)) →
  (holes : ∀ i → WPos (codeᵂ G) tree i → Carrier (emptyEnv i)) →
  _≈_ (Sem A)
    (to p ((tree , holes) , u))
    (paraGo (prAlgebra {T = A} {U = B} {G = G} h u) tree holes)
pr-unique-treeᵉ {A} {B} {G} {h} {p} premise u (sup s children) holes =
  transˢ (Sem A)
    (resp p
      (symˢ (Sem (ind G)) (con-outᵉ {G = G} x) , reflˢ (Sem B)))
    (transˢ (Sem A)
      (premise (layerClosed , u))
      (transˢ (Sem A)
        (resp h
          ( symˢ (Sem (G [ A `× ind G ]))
              (paraArgs-openᵖ {A = A} {B = B} {G = G} p u yOpen)
          , reflˢ (Sem B)))
        (resp h
          ( resp (subst←ᵉ G (σ₀ (A `× ind G)) emptyEnv)
              (unpackᵉ-resp G envAInd layer≈)
          , reflˢ (Sem B)))))
  where
    x : Carrier (Sem (ind G))
    x = sup s children , holes

    envAInd : Env 1
    envAInd = prArgEnv A G

    layer : Cont.Value (codeᵂ G) (λ i → Carrier (prIndEnv G i))
    layer = outClosedᵉ {G = G} x

    yOpen : Carrier (Semᵉ G (prIndEnv G))
    yOpen = unpackᵉ-to G (prIndEnv G) layer

    layerClosed : Carrier (Sem (G [ ind G ]))
    layerClosed = to (subst←ᵉ G (σ₀ (ind G)) emptyEnv) yOpen

    layerPr≈ : ValueEq (codeᵂ G) envAInd
      (paraLayerFromPackᵖ {A = A} {B = B} {G = G} G p u yOpen)
      (paraLayerFromPackᵉ {A = A} {B = B} {G = G} G h u yOpen)
    layerPr≈
      with packᵉ-to G (prIndEnv G) yOpen
         | pack-unpackᵉ G (prIndEnv G) layer
    ... | .s , values | value≈ pointwise =
      value≈ λ { zero q →
        let actualChild : Carrier (Sem (ind G))
            actualChild = children q , λ i r → holes i (belowW q r)

            child≈ : _≈_ (Sem (ind G))
              (proj₁ (values zero q) , λ ())
              actualChild
            child≈ =
              transˢ (Sem (ind G))
                (closedInd-normalize {G = G} (values zero q))
                (transˢ (Sem (ind G))
                  (pointwise zero q)
                  (fix-sym (codeᵂ G) emptyEnv
                    (forget-empty-holes (codeᵂ G) actualChild)))
        in
        transˢ (Sem A)
          (resp p (child≈ , reflˢ (Sem B)))
          (transˢ (Sem A)
            (pr-unique-treeᵉ {A = A} {B = B} {G = G} {h = h} {p = p}
              premise u (children q) (λ i r → holes i (belowW q r)))
            (symˢ (Sem A)
              (resp (Prᵉ {T = A} {U = B} {G = G} h)
                (child≈ , reflˢ (Sem B)))))
        , reflˢ (Sem (ind G)) }

    layer≈ : ValueEq (codeᵂ G) envAInd
      (paraLayerFromPackᵖ {A = A} {B = B} {G = G} G p u yOpen)
      (paraLayer→subst {T = A} {G = G}
        (paraLayerC {D = codeᵂ G} {ρ = emptyEnv} {A = Carrier (Sem A)}
          (prAlgebra {T = A} {U = B} {G = G} h u)
          x))
    layer≈ =
      value-trans (codeᵂ G) envAInd
        layerPr≈
        (value-trans (codeᵂ G) envAInd
          (value-sym (codeᵂ G) envAInd
            (paraLayerCon-packᵉ {A = A} {B = B} {G = G} h u yOpen))
          (paraLayerCon-outᵉ {A = A} {B = B} {G = G} h u x))

Pr-uniqueᵉ : ∀ {A B} {G : Ty HO 1}
  {h : Hom ((G [ A `× ind G ]) `× B) A}
  {p : Hom (ind G `× B) A} →
  _≈ᴴ_ {T = (G [ ind G ]) `× B} {U = A}
    (p ∘⇒ map×ᴹᵉ {T = ind G} {U = G [ ind G ]} {V = B} {W = B}
          (conᵉ {G = G}) (id⇒ {A = Sem B}))
    (h ∘⇒ paraArgsᵉ {T = A} {U = B} G p) →
  _≈ᴴ_ {T = ind G `× B} {U = A}
    p
    (Prᵉ {T = A} {U = B} {G = G} h)
Pr-uniqueᵉ {A} {B} {G} {h} {p} premise (x , u) =
  pr-unique-treeᵉ {A = A} {B = B} {G = G} {h = h} {p = p}
    premise u (proj₁ x) (proj₂ x)

model : PRHO.Model Level.zero
model = record
  { structure = structure
  ; _≈ᴹ_ = λ {T} {U} → _≈ᴴ_ {T = T} {U = U}
  ; ≈-reflᴹ = λ {U = U} x → reflˢ (Sem U)
  ; ≈-symᴹ = λ {U = U} p x → symˢ (Sem U) (p x)
  ; ≈-transᴹ = λ {U = U} p q x → transˢ (Sem U) (p x) (q x)
  ; C-congᴹ = λ {D = D} {f′ = f′} {g = g} p q x →
      transˢ (Sem D) (p (to g x)) (resp f′ (q x))
  ; pair-congᴹ = λ p q x → p x , q x
  ; case-congᴹ = λ p q → λ { (inj₁ x) → p x ; (inj₂ y) → q y }
  ; lam-congᴹ = λ p x y → p (x , y)
  ; fmap-congᴹ = fmap-congᵉ
  ; Pr-congᴹ = λ {A} {B} {G} {h} {h′} →
      Pr-congᵉ {A = A} {B = B} {G = G} {h = h} {h′ = h′}
  ; C-idˡᴹ = λ {B = B} x → reflˢ (Sem B)
  ; C-idʳᴹ = λ {B = B} x → reflˢ (Sem B)
  ; C-assocᴹ = λ {E = E} x → reflˢ (Sem E)
  ; fmap-idᴹ = fmap-idᵉ
  ; fmap-Cᴹ = fmap-Cᵉ
  ; fmap-βᶜᴹ = fmap-βᶜᵉ
  ; strength-naturalˡᴹ = strength-naturalˡᵉ
  ; strength-naturalʳᴹ = strength-naturalʳᵉ
  ; strength-π₁ᴹ = strength-π₁ᵉ
  ; strength-βᶜᴹ = strength-βᶜᵉ
  ; 𝟙-uniqueᴹ = λ x → tt
  ; 𝟘-uniqueᴹ = λ ()
  ; ×-β₁ᴹ = λ {B = B} x → reflˢ (Sem B)
  ; ×-β₂ᴹ = λ {D = D} x → reflˢ (Sem D)
  ; ×-ηᴹ = λ {B = B} {D = D} x → reflˢ (Sem B) , reflˢ (Sem D)
  ; +-β₁ᴹ = λ {D = D} x → reflˢ (Sem D)
  ; +-β₂ᴹ = λ {D = D} x → reflˢ (Sem D)
  ; +-ηᴹ = λ {D = D} → λ { (inj₁ x) → reflˢ (Sem D) ; (inj₂ y) → reflˢ (Sem D) }
  ; ⇒-βᴹ = λ {D = D} x → reflˢ (Sem D)
  ; ⇒-ηᴹ = λ {D = D} x y → reflˢ (Sem D)
  ; Pr-βᴹ = λ {A} {B} {G} {h} →
      Pr-βᵉ {A = A} {B = B} {G = G} {h = h}
  ; Pr-uniqueᴹ = λ {A} {B} {G} {h} {p} →
      Pr-uniqueᵉ {A = A} {B = B} {G = G} {h = h} {p = p}
  }

model-structure : PRHO.Model.structure model ≡ structure
model-structure = refl
