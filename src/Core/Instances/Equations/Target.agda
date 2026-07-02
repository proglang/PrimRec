{-# OPTIONS --safe #-}

module Core.Instances.Equations.Target where

open import Data.Fin using (Fin; zero)
open import Data.Nat using (ℕ; _+_)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map)

open import Core.PRFO
import Core.Equations.PRFO as CoreEq
open import Core.Instances.Common

tupleᴾ : ∀ {X T n} → Vec (X →ᴾ T) n → X →ᴾ vec T n
tupleᴾ [] = `⊤
tupleᴾ (f ∷ fs) = `# f (tupleᴾ fs)

NatF : Ty FO 1
NatF = `𝟙 `+ ` zero

Nat : TY FO
Nat = ind NatF

nat-P-handler : ∀ {n} →
  (vec Nat n →ᴾ Nat) → (vec Nat (2 + n) →ᴾ Nat) →
  (NatF [ Nat `× Nat ]) `× vec Nat n →ᴾ Nat
nat-P-handler g h =
  C (`case (C g π₂) (C h assoc-×)) dist-+-×

nat-F-handler : ∀ {n} →
  (vec Nat n →ᴾ Nat) → (vec Nat (1 + n) →ᴾ Nat) →
  (NatF [ Nat `× Nat ]) `× vec Nat n →ᴾ Nat
nat-F-handler g h =
  C (`case (C g π₂)
           (C h (`# (C π₁ π₁) π₂)))
    dist-+-×

infix 4 _≈ᴵ_

data _≈ᴵ_ : ∀ {T U : TY FO} → T →ᴾ U → T →ᴾ U → Set where
  core : ∀ {T U : TY FO} {f g : T →ᴾ U} →
    f CoreEq.≈ g → f ≈ᴵ g
  symᴵ : ∀ {T U : TY FO} {f g : T →ᴾ U} →
    f ≈ᴵ g → g ≈ᴵ f
  transᴵ : ∀ {T U : TY FO} {f g h : T →ᴾ U} →
    f ≈ᴵ g → g ≈ᴵ h → f ≈ᴵ h
  C-congᴵ : ∀ {A B D : TY FO}
    {f f′ : B →ᴾ D} {g g′ : A →ᴾ B} →
    f ≈ᴵ f′ → g ≈ᴵ g′ → C f g ≈ᴵ C f′ g′
  `#-congᴵ : ∀ {A B D : TY FO}
    {f f′ : A →ᴾ B} {g g′ : A →ᴾ D} →
    f ≈ᴵ f′ → g ≈ᴵ g′ → `# f g ≈ᴵ `# f′ g′
  `case-congᴵ : ∀ {A B D : TY FO}
    {f f′ : A →ᴾ D} {g g′ : B →ᴾ D} →
    f ≈ᴵ f′ → g ≈ᴵ g′ →
    `case f g ≈ᴵ `case f′ g′
  P-congᴵ : ∀ {A B : TY FO} {G : Ty FO 1}
    {h h′ : (G [ A `× ind G ]) `× B →ᴾ A} →
    h ≈ᴵ h′ →
    P {G = G} {T = A} {U = B} h ≈ᴵ P {G = G} {T = A} {U = B} h′

  paraHandler-congᴵ : ∀ {k n} (rs : Vec ℕ k)
    {hs ks : (i : Fin k) →
      vec (Tree rs) ((lookup rs i + lookup rs i) + n) →ᴾ Tree rs} →
    ((i : Fin k) → hs i ≈ᴵ ks i) →
    paraHandler rs hs ≈ᴵ paraHandler rs ks

  P-β-branch : ∀ {k n} (rs : Vec ℕ k)
    (steps : (i : Fin k) →
      vec (Tree rs) ((lookup rs i + lookup rs i) + n) →ᴾ Tree rs)
    {X : TY FO} (i : Fin k)
    (children : Vec (X →ᴾ Tree rs) (lookup rs i))
    (parameters : Vec (X →ᴾ Tree rs) n) →
    let rec = P {G = Branches rs} {T = Tree rs} {U = vec (Tree rs) n}
                (paraHandler rs steps)
        parameter-tuple = tupleᴾ parameters
        results = map (λ child → C rec (`# child parameter-tuple)) children
    in
    C rec (`# (C (conᴾ rs i) (tupleᴾ children)) parameter-tuple)
      ≈ᴵ
    C (steps i) (tupleᴾ ((results ++ children) ++ parameters))

  P-β-zero : ∀ {n X} (g : vec Nat n →ᴾ Nat)
    (h : vec Nat (2 + n) →ᴾ Nat)
    (parameters : Vec (X →ᴾ Nat) n) →
    let rec = P {G = NatF} {T = Nat} {U = vec Nat n} (nat-P-handler g h)
        parameter-tuple = tupleᴾ parameters
        zeroᴾ = C (C (roll {G = NatF}) ι₁) (`⊤ {T = X})
    in
    C rec (`# zeroᴾ parameter-tuple) ≈ᴵ C g parameter-tuple

  P-β-suc : ∀ {n X} (g : vec Nat n →ᴾ Nat)
    (h : vec Nat (2 + n) →ᴾ Nat)
    (counter : X →ᴾ Nat)
    (parameters : Vec (X →ᴾ Nat) n) →
    let rec = P {G = NatF} {T = Nat} {U = vec Nat n} (nat-P-handler g h)
        parameter-tuple = tupleᴾ parameters
        successor = C (C (C (roll {G = NatF}) ι₂) π₁)
                      (`# counter (`⊤ {T = X}))
        result = C rec (`# counter parameter-tuple)
    in
    C rec (`# successor parameter-tuple) ≈ᴵ
    C h (tupleᴾ ((result ∷ counter ∷ []) ++ parameters))

  F-β-zero : ∀ {n X} (g : vec Nat n →ᴾ Nat)
    (h : vec Nat (1 + n) →ᴾ Nat)
    (parameters : Vec (X →ᴾ Nat) n) →
    let rec = P {G = NatF} {T = Nat} {U = vec Nat n} (nat-F-handler g h)
        parameter-tuple = tupleᴾ parameters
        zeroᴾ = C (C (roll {G = NatF}) ι₁) (`⊤ {T = X})
    in
    C rec (`# zeroᴾ parameter-tuple) ≈ᴵ C g parameter-tuple

  F-β-suc : ∀ {n X} (g : vec Nat n →ᴾ Nat)
    (h : vec Nat (1 + n) →ᴾ Nat)
    (counter : X →ᴾ Nat)
    (parameters : Vec (X →ᴾ Nat) n) →
    let rec = P {G = NatF} {T = Nat} {U = vec Nat n} (nat-F-handler g h)
        parameter-tuple = tupleᴾ parameters
        successor = C (C (C (roll {G = NatF}) ι₂) π₁)
                      (`# counter (`⊤ {T = X}))
        result = C rec (`# counter parameter-tuple)
    in
    C rec (`# successor parameter-tuple) ≈ᴵ
    C h (tupleᴾ (result ∷ parameters))
