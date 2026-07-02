{-# OPTIONS --safe #-}

module Core.Instances.Concrete.Nat where

open import Data.Fin using (zero)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (refl)

import PR-Nat as Source
open import Core.PRFO
open import Core.Semantics.Inductive
open import Core.Semantics.Types
open import Core.Instances.Common
open import Core.Instances.Nat
open import Core.Instances.Concrete.Evaluator
open import Core.Instances.Concrete.Supported

flatNatF : Flat NatF
flatNatF = flat-+ flat-𝟙 flat-`

pHandler : ∀ {n} → Source.PR n → Source.PR (2 Data.Nat.+ n) →
  (NatF [ Nat `× Nat ]) `× vec Nat n →ᴾ Nat
pHandler g h =
  C (`case (C (compile g) π₂) (C (compile h) assoc-×)) dist-+-×

fHandler : ∀ {n} → Source.PR n → Source.PR (1 Data.Nat.+ n) →
  (NatF [ Nat `× Nat ]) `× vec Nat n →ᴾ Nat
fHandler g h =
  C (`case (C (compile g) π₂)
           (C (compile h) (`# (C π₁ π₁) π₂)))
    dist-+-×

supported : ∀ {n} (p : Source.PR n) → Supported (compile p)
supported* : ∀ {m n} (ps : Vec (Source.PR n) m) → Supported (compile* ps)

supported-pHandler : ∀ {n} (g : Source.PR n) (h : Source.PR (2 Data.Nat.+ n)) →
  Supported (pHandler g h)
supported-pHandler g h =
  s-C
    (s-case (s-C (supported g) s-π₂)
            (s-C (supported h) supported-assoc))
    s-dist

supported-fHandler : ∀ {n} (g : Source.PR n) (h : Source.PR (1 Data.Nat.+ n)) →
  Supported (fHandler g h)
supported-fHandler g h =
  s-C
    (s-case (s-C (supported g) s-π₂)
            (s-C (supported h) (s-# (s-C s-π₁ s-π₁) s-π₂)))
    s-dist

supported Source.Z = s-C (s-roll flatNatF) s-ι₁
supported Source.σ = s-C (s-C (s-roll flatNatF) s-ι₂) s-π₁
supported (Source.π i) = supported-lookup i
supported (Source.C f fs) = s-C (supported f) (supported* fs)
supported (Source.P g h) = s-P NatF flatNatF (supported-pHandler g h)
supported (Source.F g h) = s-P NatF flatNatF (supported-fHandler g h)

supported* [] = s-⊤
supported* (p ∷ ps) = s-# (supported p) (supported* ps)

encode : ℕ → Sem Nat
encode zero = node (inj₁ tt) λ ()
encode (suc n) = node (inj₂ tt) λ { refl → encode n }

encode* : Vec ℕ n → Sem (vec Nat n)
encode* [] = tt
encode* (x ∷ xs) = encode x , encode* xs

data Related : Sem Nat → ℕ → Set where
  related-zero : ∀ {children} → Related (node (inj₁ tt) children) zero
  related-suc : ∀ {children n} → Related (children refl) n →
                Related (node (inj₂ tt) children) (suc n)

data Related* : (n : ℕ) → Sem (vec Nat n) → Vec ℕ n → Set where
  related-[] : Related* zero tt []
  related-∷ : ∀ {k x n xs ns} → Related x n → Related* k xs ns →
              Related* (suc k) (x , xs) (n ∷ ns)

encode-related : (n : ℕ) → Related (encode n) n
encode-related zero = related-zero
encode-related (suc n) = related-suc (encode-related n)

encode-related* : (xs : Vec ℕ n) → Related* n (encode* xs) xs
encode-related* [] = related-[]
encode-related* (x ∷ xs) = related-∷ (encode-related x) (encode-related* xs)

lookup-related : ∀ (i : Data.Fin.Fin n) {values : Sem (vec Nat n)} {xs : Vec ℕ n} →
  Related* n values xs → Related (eval (supported-lookup i) values) (lookup xs i)
lookup-related zero (related-∷ rx rxs) = rx
lookup-related (Data.Fin.suc i) (related-∷ rx rxs) = lookup-related i rxs

correct : ∀ {n} (p : Source.PR n) {values : Sem (vec Nat n)} {xs : Vec ℕ n} →
  Related* n values xs → Related (eval (supported p) values) (Source.eval p xs)
correct* : ∀ {m n} (ps : Vec (Source.PR n) m)
  {values : Sem (vec Nat n)} {xs : Vec ℕ n} →
  Related* n values xs → Related* m (eval (supported* ps) values) (Source.eval* ps xs)

correct Source.Z related-[] = related-zero
correct Source.σ (related-∷ rx related-[]) = related-suc rx
correct (Source.π i) related = lookup-related i related
correct (Source.C f fs) related = correct f (correct* fs related)
correct {n = suc n} (Source.P g h) {values = tree , values} {xs = x ∷ xs}
  (related-∷ first parameters) = go first
  where
  go : ∀ {tree′ x′} → Related tree′ x′ →
    Related
      (paraGo
        (paraAlgebra {G = NatF} {T = Nat} {U = vec Nat n}
          flatNatF (eval (supported-pHandler g h)) values)
        tree′ (λ ()))
            (Source.eval (Source.P g h) (x′ ∷ xs))
  go related-zero = correct g parameters
  go (related-suc child) =
    correct h (related-∷ (go child) (related-∷ child parameters))
correct {n = suc n} (Source.F g h) {values = tree , values} {xs = x ∷ xs}
  (related-∷ first parameters) = go first
  where
  go : ∀ {tree′ x′} → Related tree′ x′ →
    Related
      (paraGo
        (paraAlgebra {G = NatF} {T = Nat} {U = vec Nat n}
          flatNatF (eval (supported-fHandler g h)) values)
        tree′ (λ ()))
            (Source.eval (Source.F g h) (x′ ∷ xs))
  go related-zero = correct g parameters
  go (related-suc child) = correct h (related-∷ (go child) parameters)

correct* [] related = related-[]
correct* (p ∷ ps) related = related-∷ (correct p related) (correct* ps related)

correct-encoded : ∀ {n} (p : Source.PR n) (xs : Vec ℕ n) →
  Related (eval (supported p) (encode* xs)) (Source.eval p xs)
correct-encoded p xs = correct p (encode-related* xs)
