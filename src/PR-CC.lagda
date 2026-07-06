\begin{code}
module PR-CC where

open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂; <_,_>)
open import Function using (_∘_; const)
open import Utils


----------------------------------------------------------------------
-- primitive recursion with ℕ, 𝟙, and ×
-- generalizes ℕ-vector valued version
----------------------------------------------------------------------

infix 6 _→ᴾ_
infix 7 _`×_

data Ty : Set where
  `ℕ `𝟙 : Ty
  _`×_  : Ty → Ty → Ty

variable
  T U V : Ty

data _→ᴾ_ : Ty → Ty → Set where
  Pr : (g : U →ᴾ T)
    → (h : (T `× `ℕ) `× U →ᴾ T)
    → (`ℕ `× U →ᴾ T)
  C : (f : U →ᴾ V)
    → (g : T →ᴾ U)
    → (T →ᴾ V)
  σ : `ℕ →ᴾ `ℕ
  Z : `𝟙 →ᴾ `ℕ
  `0 : T →ᴾ `𝟙
  `# : (f : T →ᴾ U)
     → (g : T →ᴾ V)
     → (T →ᴾ U `× V)
  π₁ : U `× V →ᴾ U
  π₂ : U `× V →ᴾ V

⟦_⟧ᵀ : Ty → Set
⟦ `ℕ ⟧ᵀ    = ℕ
⟦ `𝟙 ⟧ᵀ     = ⊤
⟦ T `× U ⟧ᵀ = ⟦ T ⟧ᵀ × ⟦ U ⟧ᵀ

⟦_⟧ᴱ : (T →ᴾ U) → ⟦ T ⟧ᵀ → ⟦ U ⟧ᵀ
⟦ Pr g h ⟧ᴱ (zero , u)  = ⟦ g ⟧ᴱ u
⟦ Pr g h ⟧ᴱ (suc n , u) = ⟦ h ⟧ᴱ (((⟦ Pr g h ⟧ᴱ (n , u)) , n) , u)
⟦ C f g ⟧ᴱ             = ⟦ f ⟧ᴱ ∘ ⟦ g ⟧ᴱ
⟦ σ ⟧ᴱ                 = suc
⟦ Z ⟧ᴱ                 = const 0
⟦ `0 ⟧ᴱ                = const tt
⟦ `# f g ⟧ᴱ            = < ⟦ f ⟧ᴱ , ⟦ g ⟧ᴱ >
⟦ π₁ ⟧ᴱ                = proj₁
⟦ π₂ ⟧ᴱ                = proj₂
\end{code}
