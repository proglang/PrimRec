module PR-NatsVec where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup)

open import Utils

----------------------------------------------------------------------
-- vector-valued pr on ℕ
-- PR m n encodes functions ℕᵐ → ℕⁿ
----------------------------------------------------------------------

data PR : ℕ → ℕ → Set where
  `0 : PR m 0
  Z : PR 0 1
  σ : PR 1 1
  π : (i : Fin m) → PR m 1
  C : (g : PR m n) → (f : PR o m) → PR o n
  ♯ : (g : PR m n) → (f : PR m o) → PR m (n + o)
  P : (g : PR m n) → (h : PR (n + (suc m)) n) → PR (suc m) n

eval : PR m n → Vec ℕ m → Vec ℕ n
eval `0 v* = []
eval Z [] = 0 ∷ []
eval σ (x ∷ []) = suc x ∷ []
eval (π i) v* = lookup v* i ∷ []
eval (C g f) v* = eval g (eval f v*)
eval (♯ g f) v* = eval g v* ++ eval f v*
eval (P g h) (zero ∷ v*) = eval g v*
eval (P g h) (suc x ∷ v*) = eval h (eval (P g h) (x ∷ v*) ++ x ∷ v*)
