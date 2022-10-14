\begin{code}
module NatsVec-CC where

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Product using (_×_; proj₁; proj₂; <_,_>) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup)


open import Utils

import PR-NatsVec as NV
open import PR-CC as CC

-- type translation

T⟦_⟧ᵀ : ℕ → Ty
T⟦ zero ⟧ᵀ = `𝟙
T⟦ suc m ⟧ᵀ = `ℕ `× T⟦ m ⟧ᵀ

-- value translation

T⟦_⟧ⱽ : Vec ℕ m → ⟦ T⟦ m ⟧ᵀ ⟧ᵀ
T⟦ [] ⟧ⱽ = tt
T⟦ x ∷ v ⟧ⱽ = ⟨ x , T⟦ v ⟧ⱽ ⟩

-- some type isomorphisms

identˡ : `𝟙 `× T →ᴾ T
identˡ = π₂

identʳ : T `× `𝟙 →ᴾ T
identʳ = π₁

assocˡ : (T `× U) `× V →ᴾ T `× (U `× V)
assocˡ = `# (C π₁ π₁) (`# (C π₂ π₁) π₂)

assocʳ : T `× (U `× V) →ᴾ (T `× U) `× V
assocʳ = `# (`# π₁ (C π₁ π₂)) (C π₂ π₂)

iso-+ : ∀ n o → T⟦ n ⟧ᵀ `× T⟦ o ⟧ᵀ →ᴾ T⟦ n + o ⟧ᵀ
iso-+ zero o = identˡ
iso-+ (suc n) o = C (`# π₁ (C (iso-+ n o) π₂)) assocˡ

ilookup : (i : Fin m) → T⟦ m ⟧ᵀ →ᴾ `ℕ
ilookup zero = π₁
ilookup (suc i) = C (ilookup i) π₂

-- expression translation

T⟦_⟧ : NV.PR m n → T⟦ m ⟧ᵀ →ᴾ T⟦ n ⟧ᵀ
T⟦ NV.`0 ⟧ = `0
T⟦ NV.Z ⟧ = `# Z `0
T⟦ NV.σ ⟧ = `# (C σ π₁) `0
T⟦ NV.π i ⟧ = `# (ilookup i) `0
T⟦ NV.C f g ⟧ = C T⟦ f ⟧ T⟦ g ⟧
T⟦ NV.♯ f g ⟧ = C (iso-+ _ _) (`# T⟦ f ⟧ T⟦ g ⟧)
T⟦ NV.P g h ⟧ = P T⟦ g ⟧ (C (C T⟦ h ⟧ (iso-+ _ _)) assocˡ)
T⟦ NV.P' g h ⟧ = P T⟦ g ⟧ (C (C T⟦ h ⟧ (iso-+ _ _)) assocˡ)

lemma-lookup : (v : Vec ℕ m) (i : Fin m) → lookup v i ≡  ⟦ ilookup i ⟧ᴱ T⟦ v ⟧ⱽ
lemma-lookup (x ∷ _) zero = refl
lemma-lookup (_ ∷ v) (suc i) = lemma-lookup v i

lemma-iso-+ : (v : Vec ℕ n) (w : Vec ℕ o) → T⟦ v ++ w ⟧ⱽ ≡ ⟦ iso-+ n o ⟧ᴱ ⟨ T⟦ v ⟧ⱽ , T⟦ w ⟧ⱽ ⟩
lemma-iso-+ [] w = refl
lemma-iso-+ (x ∷ v) w rewrite  lemma-iso-+ v w = refl

{-# TERMINATING #-}
sound : ∀ (p : NV.PR m n) (v : Vec ℕ m) → T⟦ NV.eval p v ⟧ⱽ ≡ ⟦ T⟦ p ⟧ ⟧ᴱ T⟦ v ⟧ⱽ
sound NV.`0 v = refl
sound NV.Z [] = refl
sound NV.σ [ x ] = refl
sound (NV.π i) v rewrite lemma-lookup v i = refl
sound (NV.C f g) v rewrite sound f (NV.eval g v) | sound g v = refl
sound (NV.♯ f g) v rewrite sym (sound f v) | sym (sound g v) = lemma-iso-+ (NV.eval f v) (NV.eval g v)
sound (NV.P g h) (zero ∷ v) = sound g v
sound (NV.P g h) (suc i ∷ v)
  rewrite
  sound h (NV.eval (NV.P g h) (i ∷ v) ++ i ∷ v)
  = cong ⟦ T⟦ h ⟧ ⟧ᴱ (trans (lemma-iso-+ (NV.eval (NV.P g h) (i ∷ v)) (i ∷ v))
                           (cong (λ ih → ⟦ iso-+ _ _ ⟧ᴱ ⟨ ih , ⟨ i , T⟦ v ⟧ⱽ ⟩ ⟩)
                                 (sound (NV.P g h) (i ∷ v))))
sound (NV.P' g h) (zero ∷ v) = sound g v
sound (NV.P' g h) (suc i ∷ v) 
  rewrite
  sound h (NV.eval (NV.P' g h) (i ∷ v) ++ i ∷ v)
  = cong ⟦ T⟦ h ⟧ ⟧ᴱ (trans (lemma-iso-+ (NV.eval (NV.P' g h) (i ∷ v)) (i ∷ v))
                           (cong (λ ih → ⟦ iso-+ _ _ ⟧ᴱ ⟨ ih , ⟨ i , T⟦ v ⟧ⱽ ⟩ ⟩)
                                 (sound (NV.P' g h) (i ∷ v))))

\end{code}
