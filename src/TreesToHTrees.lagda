\begin{code}
module TreesToHTrees where

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; suc; zero; _*_; _+_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head)
open import Data.Vec.Properties using (lookup-map)
open import Data.List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_; _++_ to _++ᴸ_; length to lengthᴸ; map to mapᴸ)
open import Function using (_∘_; const)

open import Utils hiding (repeat; ++-repeat; map-repeat)

import PR-Trees as Trees
import PR-HTrees as HTrees

-- utilities

repeat : ∀ {ℓ} {A : Set ℓ} → A → (n : ℕ) → Vec A n
repeat a zero = []
repeat a (suc n) = a ∷ repeat a n

++-repeat : ∀ {m} {n} {ℓ} {A : Set ℓ} (x : A) → repeat x (m + n) ≡ repeat x m ++ repeat x n
++-repeat {zero} x = refl
++-repeat {suc m} x = cong (x ∷_) (++-repeat {m} x)

map-repeat : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → ∀ n (x : A) (f : A → B) → repeat (f x) n ≡ map f (repeat x n)
map-repeat zero x f = refl
map-repeat (suc n) x f rewrite map-repeat n x f = refl


-- pr on heterogeneous trees simulates pr on trees

make-sig : Trees.Ranked → HTrees.Sorted ⊤
make-sig R = HTrees.mkSorted (Trees.rank R) (repeat tt ∘ Trees.rank R) (const tt)

make-sorting : (n : ℕ) → Vec ⊤ n × ⊤
make-sorting n = ⟨ repeat tt n , tt ⟩

⟦_⟧  : ∀ {R : Trees.Ranked}
  → Trees.PR R n
  → HTrees.PR (make-sig R) (make-sorting n)
⟦_⟧* : ∀ {R : Trees.Ranked}
  → Vec (Trees.PR R n) m
  → HTrees.PR* (make-sig R) ⟨ repeat tt n , repeat tt m ⟩

⟦ Trees.σ a ⟧ = HTrees.σ a
⟦ Trees.π i ⟧ = HTrees.π i
⟦ Trees.C f g* ⟧ = HTrees.C ⟦ f ⟧ ⟦ g* ⟧*
⟦_⟧ {suc n} {R = R} (Trees.P h) = HTrees.P (const tt) λ a → subst (λ ss → HTrees.PR (make-sig R) ⟨ ss , tt ⟩) (eq-repeat a) ⟦ h a ⟧
  where
    eq-repeat : ∀ a →
      repeat tt (HTrees.rank (make-sig R) a + HTrees.rank (make-sig R) a + n)
      ≡
      (map (const tt) (HTrees.sin* (make-sig R) a) ++ HTrees.sin* (make-sig R) a) ++ repeat tt n
    eq-repeat a = begin
                    repeat tt (HTrees.rank (make-sig R) a + HTrees.rank (make-sig R) a + n)
                  ≡⟨ ++-repeat {HTrees.rank (make-sig R) a + HTrees.rank (make-sig R) a} tt ⟩
                    repeat tt (HTrees.rank (make-sig R) a + HTrees.rank (make-sig R) a) ++ repeat tt n
                  ≡⟨ cong (_++ repeat tt n) (++-repeat {Trees.rank R a} tt) ⟩
                    (repeat tt (Trees.rank R a) ++ repeat tt (HTrees.rank (make-sig R) a)) ++ repeat tt n
                  ≡⟨ cong (_++ repeat tt n) (cong (_++ repeat tt (Trees.rank R a)) (map-repeat (Trees.rank R a) tt (const tt))) ⟩
                    (map (const tt) (HTrees.sin* (make-sig R) a) ++ HTrees.sin* (make-sig R) a) ++ repeat tt n
                  ∎

⟦ [] ⟧* = HTrees.[]
⟦ p ∷ p* ⟧* = ⟦ p ⟧ HTrees.∷ ⟦ p* ⟧*

⟦_⟧ⱽ  : ∀ {R} → Trees.Term R → HTrees.Term (make-sig R) tt
⟦_⟧ⱽ* : ∀ {R} → Vec (Trees.Term R) n → HTrees.Term* (make-sig R) (repeat tt n)

⟦ Trees.con a x* ⟧ⱽ = HTrees.con a ⟦ x* ⟧ⱽ*
⟦ [] ⟧ⱽ* = HTrees.[]
⟦ x ∷ x* ⟧ⱽ* = ⟦ x ⟧ⱽ HTrees.∷ ⟦ x* ⟧ⱽ*

lookup-alookup : ∀ {R} (i : Fin n) (v* : Vec (Trees.Term R) n)
  → lookup (map ⟦_⟧ⱽ v*) i ≡ HTrees.alookup ⟦ v* ⟧ⱽ* i
lookup-alookup zero (x ∷ v*) = refl
lookup-alookup (suc i) (x ∷ v*) = lookup-alookup i v*


sound  : ∀ {R} (p : Trees.PR R n) (v* : Vec (Trees.Term R) n)
  → ⟦ Trees.eval p v* ⟧ⱽ ≡ HTrees.eval ⟦ p ⟧ ⟦ v* ⟧ⱽ*
sound* : ∀ {R} (p* : Vec (Trees.PR R n) m) (v* : Vec (Trees.Term R) n)
  → ⟦ Trees.eval* p* v* ⟧ⱽ* ≡ HTrees.eval* ⟦ p* ⟧* ⟦ v* ⟧ⱽ*

sound (Trees.σ a) v* = refl
sound (Trees.π i) v* = begin
                         ⟦ lookup v* i ⟧ⱽ
                       ≡˘⟨ lookup-map i ⟦_⟧ⱽ v* ⟩
                         lookup (map ⟦_⟧ⱽ v*) i
                       ≡⟨ lookup-alookup i v* ⟩
                         HTrees.alookup ⟦ v* ⟧ⱽ* i
                       ∎
sound (Trees.C f g*) v* rewrite sound f (Trees.eval* g* v*) | sound* g* v* = refl
sound (Trees.P h) v* = {!!}

sound* [] v* = refl
sound* (p ∷ p*) v* rewrite sound p v* | sound* p* v* = refl
\end{code}
