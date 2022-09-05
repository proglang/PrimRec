module System-T where

open import Data.Fin using (Fin; suc; zero; fromℕ; opposite; raise)
open import Data.Nat using (ℕ; suc; zero; _∸_; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; +-comm)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head; init)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)



open import PR-Nat
open import Utils



-- size of context and number of arguments

data Exp : ℕ → ℕ  → Set where
    Var : Fin n → Exp   n zero
    Lam : Exp (suc n) m → Exp n (suc m)
    CZero :  Exp n zero
    Suc : Exp n (suc zero)


evalST : Exp n m → Vec ℕ n → Vec ℕ m → ℕ 
evalST (Var x) ctx args = lookup ctx x
evalST (Lam exp) ctx (x ∷ args) = evalST exp (x ∷ ctx) args
evalST CZero ctx args = 0
evalST Suc ctx [ x ] = suc x


evalSTClosed : Exp zero m → Vec ℕ m → ℕ
evalSTClosed exp args = evalST exp [] args


------------------------------------------------------------------------------
-- helper
------------------------------------------------------------------------------


prepLambdas : (n : ℕ) → (m : ℕ) →  Exp (m + n) o -> Exp n (m + o)
prepLambdas n zero  exp = exp
prepLambdas n (suc m) exp  rewrite (sym(+-suc m n))  = Lam (prepLambdas  (suc n) m exp)

------------------------------------------------------------------------------
-- constant zero-function
------------------------------------------------------------------------------

mkConstZero :  {n : ℕ} → (m : ℕ) → Exp n m 
mkConstZero zero = CZero
mkConstZero (suc m) = Lam (mkConstZero m)

------------------------------------------------------------------------------
-- projection
------------------------------------------------------------------------------


convProj'' : (m : ℕ) → (n : ℕ) → Fin (n + m)  →  Exp n m
convProj'' zero n f rewrite +-identityʳ n = Var f
convProj'' (suc m) n f rewrite +-suc n m  = Lam (convProj'' m (suc n) f)


convProj''' :  (m : ℕ) → (n : ℕ) → Fin m  → Exp n m
convProj'''  m n f = convProj'' m n (raise n (opposite {m} f))

helperFin : opposite {1} zero ≡  zero
helperFin = refl


helperFin' : ∀ {n : ℕ}  → opposite {suc n} zero ≡  fromℕ n
helperFin' {n} = refl


swapIndicesF : ∀  {m : ℕ}  {n : ℕ} → Fin (n + m)   ≡ Fin (m + n) 
swapIndicesF {m} {n}  rewrite +-comm m n  = refl


swapIndicesF' : ∀  {m : ℕ}  {n : ℕ} → Fin (n + m)   → Fin (m + n) 
swapIndicesF' {m} {n} f rewrite swapIndicesF {m} {n}  = f



eqProj'''' : ∀  (m : ℕ)  (n : ℕ) (f : Fin (n + m) ) (xs : Vec ℕ n) (ys : Vec ℕ m)  → evalST (convProj'' m n f) xs ys ≡ lookup (ys ++ xs) (swapIndicesF'   {m} {n} f)
eqProj'''' zero (suc n) zero (x ∷ xs) []  = {!   !}
eqProj'''' zero (suc n) (suc f) (x ∷ xs) [] = {!   !}
eqProj'''' (suc m) n f xs (y ∷ ys) = {!  xs !}

------------------------------------------------------------------------------
-- conversion
------------------------------------------------------------------------------


prToST : (n : ℕ) → (m : ℕ) → PR m → Exp n m 
prToST n m Z = mkConstZero m
prToST n .1 σ = Suc
prToST n m (π i) = convProj''' m n ( i)
prToST n m (C pr x) = {!   !}
prToST n .(suc _) (P pr pr₁) = {!   !}


prToST' : (m : ℕ) → PR m → Exp zero m 
prToST' m  pr = prToST zero m pr


eqPrST0 : ∀ ( pr : PR zero) → eval pr [] ≡ evalSTClosed (prToST' zero  pr) []
eqPrST0 Z = refl
eqPrST0 (C pr x)  = {!   !}


eqPrST1 : ∀ ( pr : PR 1) (n : ℕ ) → eval pr [ n ] ≡ evalSTClosed (prToST' 1 pr) [ n ]
eqPrST1 Z n = refl
eqPrST1 σ n = refl
eqPrST1 (π zero) n = refl
eqPrST1 (C pr x) n = {!   !}
eqPrST1 (P pr pr₁) n = {!   !}


eqPrST2 : ∀ ( pr : PR 2) (v : Vec ℕ 2 ) → eval pr v ≡ evalSTClosed (prToST' 2 pr) v
eqPrST2 Z [ n , m ] = refl
eqPrST2 (π zero) [ n , m ]  = refl
eqPrST2 (π (suc zero)) [ n , m ] = refl
eqPrST2 (C pr x) v = {!   !}
eqPrST2 (P pr pr₁) v = {!   !}


eqPrST3 : ∀ ( pr : PR 3) (v : Vec ℕ 3 ) → eval pr v ≡ evalSTClosed (prToST' 3  pr) v
eqPrST3 Z (n ∷ [ m , o ]) = refl
eqPrST3 (π zero) (n ∷ [ m , o ]) = refl
eqPrST3 (π (suc zero)) (n ∷ [ m , o ]) = refl
eqPrST3 (π (suc (suc zero))) (n ∷ [ m , o ]) = refl
eqPrST3 (C pr x) (n ∷ [ m , o ]) = {!   !}
eqPrST3 (P pr pr₁) (n ∷ [ m , o ]) = {!   !}


eqPrSTZ' : ∀  (n m : ℕ ) (xs : Vec ℕ n )  (ys : Vec ℕ m )→ 0 ≡ evalST (mkConstZero m) xs ys
eqPrSTZ' n zero xs ys = refl
eqPrSTZ' n (suc m) xs (y ∷ ys) rewrite eqPrSTZ' (suc n) m (y ∷ xs) ys = refl

eqPrSTZ : ∀  (n : ℕ ) (v : Vec ℕ n ) → 0 ≡ evalSTClosed (prToST' n Z) v
eqPrSTZ n v = eqPrSTZ' zero n [] v

eqPrSTn : ∀  (n : ℕ ) ( pr : PR n) (v : Vec ℕ n ) → eval pr v ≡ evalSTClosed (prToST' n  pr) v
eqPrSTn n Z v = eqPrSTZ n v
eqPrSTn 1 σ [ x ] = refl
eqPrSTn n (π i) v = {!   !}
eqPrSTn n (C pr x) v = {!   !}
eqPrSTn .(suc _) (P pr pr₁) v = {!   !}



-- eqPrSTPi : ∀  (n : ℕ ) (v : Vec ℕ n) (f : Fin n) → lookup v f ≡ evalSTClosed (prToST' n (π f)) v
-- eqPrSTPi (suc zero) (x ∷ v) zero = refl
-- eqPrSTPi (suc (suc n)) (x ∷ v) zero = {!   !}
-- eqPrSTPi (suc (suc n)) (x ∷ v) (suc f) rewrite (eqPrSTPi (suc n) v f) = {!   !}

-- eqPrSTPi' : ∀  (m n : ℕ ) (f : Fin n) (xs : Vec ℕ n) (ys : Vec ℕ m) → evalST (convProj''' n m f ) ys xs ≡ lookup  xs f
-- eqPrSTPi' zero (suc m) zero (x ∷ xs) [] = {!   !}
-- eqPrSTPi' zero (suc m) (suc f) (x ∷ xs) [] = {!   !}
-- eqPrSTPi' (suc n) m f xs ys = {!   !}












-------------------------------
data Ty : Set where
    TNat : Ty
    _⇒_ : Ty → Ty → Ty


Ctx : ℕ → Set 
Ctx n  = Vec (Ty) n

-- data Exp : {n : ℕ} → Ctx n → Ty → Set where
-- data Exp : ℕ → Ty → Set where
--     Var : Fin n → Exp n TNat
--     Lam : {t : Ty} → Exp (suc n) t → Exp n (TNat ⇒ t)  