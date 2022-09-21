\begin{code}
{-# OPTIONS --rewriting #-}
module TreesToHTrees where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)

open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; suc; zero; _*_; _+_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ;_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
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

++-repeat : ∀ {ℓ} {A : Set ℓ} m n (x : A) → repeat x (m + n) ≡ repeat x m ++ repeat x n
++-repeat zero n x = refl
++-repeat (suc m) n x = cong (x ∷_) (++-repeat m n x)
{-# REWRITE ++-repeat #-}


map-repeat : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → ∀ n (x : A) (f : A → B) → map f (repeat x n) ≡ repeat (f x) n
map-repeat zero x f = refl
map-repeat (suc n) x f rewrite map-repeat n x f = refl
{-# REWRITE map-repeat #-}

-- pr on heterogeneous trees simulates pr on trees

make-sig : Trees.Ranked → HTrees.Sorted ⊤
make-sig R = HTrees.mkSorted (Trees.rank R) (repeat tt ∘ Trees.rank R) (const tt)

make-sorting : (n : ℕ) → Vec ⊤ n × ⊤
make-sorting n = ⟨ repeat tt n , tt ⟩

⟦_⟧ⱽ  : ∀ {R} → Trees.Term R → HTrees.Term (make-sig R) tt
⟦_⟧ⱽ* : ∀ {R} → Vec (Trees.Term R) n → HTrees.Term* (make-sig R) (repeat tt n)

⟦ Trees.con a x* ⟧ⱽ = HTrees.con a ⟦ x* ⟧ⱽ*
⟦ [] ⟧ⱽ* = HTrees.[]
⟦ x ∷ x* ⟧ⱽ* = ⟦ x ⟧ⱽ HTrees.∷ ⟦ x* ⟧ⱽ*

-- this definition requires rewriting with ++-repeat to even state the type signature
++-++ᴬ : ∀ {R} {m} (v* : Vec (Trees.Term R) m) {n} (w* : Vec (Trees.Term R) n)
  → ⟦ v* ++ w* ⟧ⱽ* ≡ ⟦ v* ⟧ⱽ* HTrees.++ᴬ ⟦ w* ⟧ⱽ*
++-++ᴬ [] w* = refl
++-++ᴬ (v ∷ v*) w* = cong (⟦ v ⟧ⱽ HTrees.∷_) (++-++ᴬ v* w*)

lookup-alookup : ∀ {R} (i : Fin n) (v* : Vec (Trees.Term R) n)
  → ⟦ lookup v* i ⟧ⱽ ≡ HTrees.alookup ⟦ v* ⟧ⱽ* i
lookup-alookup zero (x ∷ v*) = refl
lookup-alookup (suc i) (x ∷ v*) = lookup-alookup i v*

⟦_⟧  : ∀ {R : Trees.Ranked}
  → Trees.PR R n
  → HTrees.PR (make-sig R) (make-sorting n)
⟦_⟧* : ∀ {R : Trees.Ranked}
  → Vec (Trees.PR R n) m
  → HTrees.PR* (make-sig R) ⟨ repeat tt n , repeat tt m ⟩

⟦ Trees.σ a ⟧ = HTrees.σ a
⟦ Trees.π i ⟧ = HTrees.π i
⟦ Trees.C f g* ⟧ = HTrees.C ⟦ f ⟧ ⟦ g* ⟧*
⟦_⟧ {suc n} {R = R} (Trees.P h) = HTrees.P (const tt) λ a → subst (λ ss → HTrees.PR (make-sig R) ⟨ ss , tt ⟩) refl ⟦ h a ⟧
  -- above line requires: REWRITE ++-repeat map-repeat
  -- where
  --   eq-repeat : ∀ a →
  --     repeat tt (HTrees.rank (make-sig R) a + HTrees.rank (make-sig R) a + n)
  --     ≡
  --     (map (const tt) (HTrees.sin* (make-sig R) a) ++ HTrees.sin* (make-sig R) a) ++ repeat tt n
  --   eq-repeat a rewrite map-repeat (Trees.rank R a) tt (const tt) = refl
    -- eq-repeat a = begin
    --                 repeat tt (HTrees.rank (make-sig R) a + HTrees.rank (make-sig R) a + n)
    --               ≡⟨ ++-repeat (HTrees.rank (make-sig R) a + HTrees.rank (make-sig R) a) _ tt ⟩
    --                 repeat tt (HTrees.rank (make-sig R) a + HTrees.rank (make-sig R) a) ++ repeat tt n
    --               ≡⟨ cong (_++ repeat tt n) (++-repeat (Trees.rank R a) _ tt) ⟩
    --                 (repeat tt (Trees.rank R a) ++ repeat tt (HTrees.rank (make-sig R) a)) ++ repeat tt n
    --               ≡⟨ cong (_++ repeat tt n) (cong (_++ repeat tt (Trees.rank R a)) (map-repeat (Trees.rank R a) tt (const tt))) ⟩
    --                 (map (const tt) (HTrees.sin* (make-sig R) a) ++ HTrees.sin* (make-sig R) a) ++ repeat tt n
    --               ∎

⟦ [] ⟧* = HTrees.[]
⟦ p ∷ p* ⟧* = ⟦ p ⟧ HTrees.∷ ⟦ p* ⟧*

{-# TERMINATING #-}
sound  : ∀ {R} (p : Trees.PR R n) (v* : Vec (Trees.Term R) n)
  → ⟦ Trees.eval p v* ⟧ⱽ ≡ HTrees.eval ⟦ p ⟧ ⟦ v* ⟧ⱽ*
sound* : ∀ {R} (p* : Vec (Trees.PR R n) m) (v* : Vec (Trees.Term R) n)
  → ⟦ Trees.eval* p* v* ⟧ⱽ* ≡ HTrees.eval* ⟦ p* ⟧* ⟦ v* ⟧ⱽ*

sound (Trees.σ a) v* = refl
sound (Trees.π i) v* = begin
                         ⟦ lookup v* i ⟧ⱽ
                       ≡⟨ lookup-alookup i v* ⟩
                         HTrees.alookup ⟦ v* ⟧ⱽ* i
                       ∎
sound (Trees.C f g*) v* rewrite sound f (Trees.eval* g* v*) | sound* g* v* = refl
sound {n = n}{R = R} (Trees.P h) (Trees.con a x* ∷ v*)
  -- rewrite sound (h a) ((map (λ x → Trees.eval (Trees.P h) (x ∷ v*)) x* ++ x*) ++ v*)
  --       | sym (++-map ⟦_⟧ⱽ (map (λ x → Trees.eval (Trees.P h) (x ∷ v*)) x* ++ x*) v*)
  = begin
      ⟦ Trees.eval (h a) ((map (λ x → Trees.eval (Trees.P h) (x ∷ v*)) x* ++ x*) ++ v*) ⟧ⱽ
    ≡⟨ sound (h a) ((map (λ x → Trees.eval (Trees.P h) (x ∷ v*)) x* ++ x*) ++ v*) ⟩
      HTrees.eval ⟦ h a ⟧ ⟦ (map (λ x → Trees.eval (Trees.P h) (x ∷ v*)) x* ++ x*) ++ v* ⟧ⱽ*
    ≡⟨ cong (HTrees.eval ⟦ h a ⟧) (++-++ᴬ (map (λ x → Trees.eval (Trees.P h) (x ∷ v*)) x* ++ x*) v*) ⟩
      HTrees.eval ⟦ h a ⟧ (⟦ map (λ x → Trees.eval (Trees.P h) (x ∷ v*)) x* ++ x* ⟧ⱽ* HTrees.++ᴬ ⟦ v* ⟧ⱽ*)
    ≡⟨ cong (λ VV → HTrees.eval ⟦ h a ⟧ (VV HTrees.++ᴬ ⟦ v* ⟧ⱽ*)) (++-++ᴬ _ x*) ⟩
      HTrees.eval ⟦ h a ⟧ ((⟦ map (λ x → Trees.eval (Trees.P h) (x ∷ v*)) x* ⟧ⱽ* HTrees.++ᴬ ⟦ x* ⟧ⱽ*) HTrees.++ᴬ ⟦ v* ⟧ⱽ*)
    ≡⟨ cong
         (λ VV →
            HTrees.eval ⟦ h a ⟧ ((VV HTrees.++ᴬ ⟦ x* ⟧ⱽ*) HTrees.++ᴬ ⟦ v* ⟧ⱽ*))
         (eq x*) ⟩
      HTrees.eval ⟦ h a ⟧
      ((HTrees.mapᴬ
        (λ i x →
           HTrees.eval (HTrees.P (const tt) (λ a₁ → ⟦ h a₁ ⟧))
           (x HTrees.∷ ⟦ v* ⟧ⱽ*))
        ⟦ x* ⟧ⱽ*
        HTrees.++ᴬ ⟦ x* ⟧ⱽ*)
       HTrees.++ᴬ ⟦ v* ⟧ⱽ*)
     ∎
  where
    eq : ∀ {k} (x* : Vec (Trees.Term R) k) →
       ⟦ map (λ x → Trees.eval (Trees.P h) (x ∷ v*)) x* ⟧ⱽ*
       ≡ HTrees.mapᴬ{ss = repeat tt k} (λ i x → HTrees.eval (HTrees.P (const tt) (λ a₁ → ⟦ h a₁ ⟧)) (x HTrees.∷ ⟦ v* ⟧ⱽ*)) ⟦ x* ⟧ⱽ*
    eq [] = refl
    eq (x ∷ x*) rewrite sound (Trees.P h) (x ∷ v*) = cong
                                                       (HTrees.eval (HTrees.P (λ _ → tt) (λ a₁ → ⟦ h a₁ ⟧))
                                                        (⟦ x ⟧ⱽ HTrees.∷ ⟦ v* ⟧ⱽ*)
                                                        HTrees.∷_)
                                                       (eq x*)

sound* [] v* = refl
sound* (p ∷ p*) v* rewrite sound p v* | sound* p* v* = refl
\end{code}
