\begin{code}
module PR-Nat where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head)

open import Utils

----------------------------------------------------------------------
-- primitive recursion on ℕ
----------------------------------------------------------------------

data PR : ℕ → Set where
  Z : PR n
  σ : PR (suc zero)
  π : (i : Fin n) → PR n
  C : PR m → Vec (PR n) m → PR n
  P : (g : PR n) → (h : PR (suc (suc n))) → PR (suc n)

eval  : PR n → Vec ℕ n → ℕ
eval* : Vec (PR n) m → Vec ℕ n → Vec ℕ m

eval Z        v*           = 0
eval σ        (x ∷ v*)     = suc x
eval (π i)    v*           = lookup v* i
eval (C f g*) v*           = eval f (eval* g* v*)
eval (P g h)  (zero ∷ v*)  = eval g v*
eval (P g h)  (suc x ∷ v*) = eval h ((eval (P g h) (x ∷ v*)) ∷ (x ∷ v*))

eval* []       v*          = []
eval* (p ∷ p*) v*          = eval p v*  ∷ eval* p* v*
\end{code}
