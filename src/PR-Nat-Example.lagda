\begin{code}
module PR-Nat-Example where

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_; _*_; _^_; _∸_; pred)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-∸-assoc; ∸-+-assoc; 0∸n≡0)
open import Data.Vec using (Vec; []; _∷_; _++_)
open import Agda.Builtin.Nat public
  using () renaming (_<_ to _<ᵇ_)

open import Utils

open import PR-Nat

----------------------------------------------------------------------
-- addition

addP : PR 2
addP = P (π zero) (C σ [ π zero ])

addP=+ : ∀ m n → eval addP [ m , n ] ≡ m + n
addP=+ zero n = refl
addP=+ (suc m) n = cong suc (addP=+ m n)

----------------------------------------------------------------------
-- multiplication

mulP : PR 2
mulP = P Z (C addP [ π (suc (suc zero)) , π zero ])

mulP=* : ∀ m n → eval mulP [ m , n ] ≡ m * n
mulP=* zero n = refl
mulP=* (suc m) n
  rewrite mulP=* m n
        | addP=+ n (m * n) = refl

----------------------------------------------------------------------
-- exponentiation

expP : PR 2
expP = C (P (C σ [ Z ]) (C mulP [ π (suc (suc zero)) , π zero ])) [ π (suc zero) , π zero ]

expP=^ : ∀ m n → eval expP [ m , n ] ≡ m ^ n
expP=^ m zero = refl
expP=^ m (suc n)
  rewrite expP=^ m n
        | mulP=* m (m ^ n) = refl

----------------------------------------------------------------------
-- predecessor

predP : PR 1
predP = P Z (π (suc zero))

predP=∸1 : ∀ m → eval predP [ m ] ≡ pred m
predP=∸1 zero = refl
predP=∸1 (suc m) = refl

----------------------------------------------------------------------
-- subtraction (monus)

subP : PR 2
subP = C (P (π zero) (C predP [ π zero ])) [ π (suc zero) , π zero ]

m∸n∸1≡m∸sucn : ∀ m n → m ∸ n ∸ 1 ≡ m ∸ suc n
m∸n∸1≡m∸sucn zero zero = refl
m∸n∸1≡m∸sucn zero (suc n) = refl
m∸n∸1≡m∸sucn (suc m) zero = refl
m∸n∸1≡m∸sucn (suc m) (suc n) = m∸n∸1≡m∸sucn m n

subP=∸ : ∀ m n → eval subP [ m , n ] ≡ m ∸ n
subP=∸ m zero = refl
subP=∸ m (suc n)
  rewrite subP=∸ m n
        | predP=∸1 (m ∸ n) = m∸n∸1≡m∸sucn m n

----------------------------------------------------------------------
-- factorial

facP : PR 1
facP = P (C σ [ Z ]) (C mulP [ π zero , C σ [ π (suc zero) ] ])

fac : ℕ → ℕ
fac zero = 1
fac (suc n) = fac n * suc n

facP=fac : ∀ m → eval facP [ m ] ≡ fac m
facP=fac zero = refl
facP=fac (suc m)
  rewrite facP=fac m
        | mulP=* (fac m) (suc m) = refl

----------------------------------------------------------------------
-- auxiliary definitions for remainder

TRUE  = 1
FALSE = 0

isZeroP : PR 1
isZeroP = P (C σ [ Z ]) Z

isZero : ℕ → ℕ
isZero zero = TRUE
isZero (suc n) = FALSE

isZeroP=isZero : ∀ m → eval isZeroP [ m ] ≡ isZero m
isZeroP=isZero zero = refl
isZeroP=isZero (suc m) = refl

--------------------

ifElseP : PR 3
ifElseP = P (π (suc zero)) (π (suc (suc zero)))

ifElse : ℕ → ℕ → ℕ → ℕ
ifElse zero n o = o
ifElse (suc m) n o = n

ifElseP=ifElse : ∀ m n o → eval ifElseP [ m , n , o ] ≡ ifElse m n o
ifElseP=ifElse zero n o = refl
ifElseP=ifElse (suc m) n o = refl

--------------------

notP : PR 1
notP = isZeroP

toBoolP : PR 1
toBoolP = P Z (C σ [ Z ])

data _~_ : ℕ → ℕ → Set where
  FF : zero ~ zero
  TT : ∀{m} → suc m ~ 1

toBool~ : ∀ m n → m ~ n → eval toBoolP [ m ] ≡ n
toBool~ .0 .0 FF = refl
toBool~ .(suc _) .1 TT = refl

toBoolP′ : PR 1
toBoolP′ = C notP [ notP ]

toBoolP=toBoolP′ : ∀ m → eval toBoolP [ m ] ≡ eval toBoolP′ [ m ]
toBoolP=toBoolP′ zero = refl
toBoolP=toBoolP′ (suc m) = refl

--------------------

smallerP : PR 2
smallerP = C toBoolP [ subP ]

smaller : ℕ → ℕ → ℕ
smaller m n with n <ᵇ m
... | false = FALSE
... | true = TRUE

subP~smaller : ∀ m n → (m ∸ n) ~ smaller m n
subP~smaller zero n rewrite 0∸n≡0 n = FF
subP~smaller (suc m) zero = TT
subP~smaller (suc m) (suc n)
  with subP~smaller m n
... | ih with n <ᵇ m
... | false = ih
... | true = ih

smallerP=smaller : ∀ m n → eval smallerP [ m , n ] ≡ smaller m n
smallerP=smaller m n rewrite subP=∸ m n = toBool~ (m ∸ n) (smaller m n) (subP~smaller m n)

-- rem m n = m % n
remGP : PR 3
remGP = C ifElseP [ C smallerP [ π (suc (suc zero)) , C σ [ π zero ] ]
                  , C σ [ π zero ]
                  , Z ]

remP : PR 2
remP = P Z remGP

-- inefficent, but unclear how to handle Nat.DivMod._%_
rem : ℕ → ℕ → ℕ
rem zero n = 0
rem (suc m) n with rem m n
... | m%n with suc m%n <ᵇ n
... | false = 0
... | true = suc m%n

remP=rem : ∀ m n → eval remP [ m , n ] ≡ rem m n
remP=rem zero n = refl
remP=rem (suc m) n
  rewrite remP=rem m n
  rewrite smallerP=smaller n (suc (rem m n))
  with suc (rem m n) <ᵇ n
... | false = refl
... | true = refl

\end{code}