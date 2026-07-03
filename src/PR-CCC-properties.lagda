\begin{code}
module PR-CCC-properties where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; [] ; _∷_; _++_; map; concat)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Vec using (Vec;[];_∷_; replicate) renaming (map to mapⱽ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ) renaming (<_,_> to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; const; flip) renaming (id to identity)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality.WithK using (≡-irrelevant)
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Utils

open import PR-CCC-ind

module FromCC where
  import PR-CC-ind as CC

  -- translation of types

  T⟦_⟧ : CC.Ty n → Ty n
  T⟦ CC.`𝟘 ⟧ = `𝟘
  T⟦ CC.`𝟙 ⟧ = `𝟙
  T⟦ T₁ CC.`× T₂ ⟧ = T⟦ T₁ ⟧ `× T⟦ T₂ ⟧
  T⟦ T₁ CC.`+ T₂ ⟧ = T⟦ T₁ ⟧ `+ T⟦ T₂ ⟧
  T⟦ CC.` x ⟧ = ` x
  T⟦ CC.ind T ⟧ = ind T⟦ T ⟧

  -- translation of types is compatible with substitution

  postulate
    extensionality : ∀ {A B : Set} {f g : A → B}
      → (∀ (x : A) → f x ≡ g x)
        -----------------------
      → f ≡ g

  lemma-ren : ∀ (ρ : CC.Ren Γ Δ) → ∀ x → ext ρ x ≡ CC.ext ρ x
  lemma-ren ρ zero = refl
  lemma-ren ρ (suc x) = refl

  trans-compat-ren : ∀ (ρ : CC.Ren Γ Δ) (T : CC.Ty Γ) → ren ρ T⟦ T ⟧ ≡ T⟦ CC.ren ρ T ⟧
  trans-compat-ren ρ CC.`𝟘 = refl
  trans-compat-ren ρ CC.`𝟙 = refl
  trans-compat-ren ρ (T₁ CC.`× T₂) = cong₂ _`×_ (trans-compat-ren ρ T₁) (trans-compat-ren ρ T₂)
  trans-compat-ren ρ (T₁ CC.`+ T₂) = cong₂ _`+_ (trans-compat-ren ρ T₁) (trans-compat-ren ρ T₂)
  trans-compat-ren ρ (CC.` x) = refl
  trans-compat-ren ρ (CC.ind T) = cong ind (trans (trans-compat-ren (extᴿ ρ) T) 
                                                  (cong (λ hole → T⟦ CC.ren hole T ⟧) (extensionality (lemma-ren ρ))) )

  trans-compat-ext : ∀ (σ : CC.Sub Γ Δ) x → T⟦ CC.extˢ σ x ⟧ ≡ extˢ (T⟦_⟧ ∘ σ) x
  trans-compat-ext σ zero = refl
  trans-compat-ext σ (suc x) = sym (trans-compat-ren suc (σ x))

  trans-compat-subst : ∀ (G : CC.Ty Γ) (σ : CC.Sub Γ Δ) → T⟦ CC.sub σ G ⟧ ≡ sub (T⟦_⟧ ∘ σ) T⟦ G ⟧
  trans-compat-subst CC.`𝟘 σ = refl
  trans-compat-subst CC.`𝟙 σ = refl
  trans-compat-subst (G₁ CC.`× G₂) σ = cong₂ _`×_ (trans-compat-subst G₁ σ) (trans-compat-subst G₂ σ)
  trans-compat-subst (G₁ CC.`+ G₂) σ = cong₂ _`+_ (trans-compat-subst G₁ σ) (trans-compat-subst G₂ σ)
  trans-compat-subst (CC.` x) σ = refl
  trans-compat-subst (CC.ind G) σ = cong ind (trans (trans-compat-subst G (CC.extˢ σ))
                                                    (cong (λ hole → sub hole T⟦ G ⟧) (extensionality (trans-compat-ext σ))))

  trans-compat-lemma : ∀ (T : CC.Ty Γ) x → T⟦ CC.σ₀ T x ⟧ ≡ σ₀ T⟦ T ⟧ x
  trans-compat-lemma T zero = refl
  trans-compat-lemma T (suc x) = refl

  trans-compat-ind : ∀ (G : CC.Ty 2) (T : CC.TY)
    → T⟦ CC.sub (CC.extˢ (CC.σ₀ T)) G ⟧
      ≡ sub (extˢ (σ₀ T⟦ T ⟧)) T⟦ G ⟧
  trans-compat-ind G T =
    trans (trans-compat-subst G (CC.extˢ (CC.σ₀ T)))
      (cong (λ hole → sub hole T⟦ G ⟧)
        (extensionality (λ x → trans (trans-compat-ext (CC.σ₀ T) x)
          (cong (λ hole → extˢ hole x)
            (extensionality (trans-compat-lemma T))))))

  trans-compat-subst-one : ∀ {n} (G : CC.Ty (suc n)) (T : CC.Ty n)
    → T⟦ CC.sub (CC.σ₀ T) G ⟧ ≡ sub (σ₀ T⟦ T ⟧) T⟦ G ⟧
  trans-compat-subst-one CC.`𝟘 T = refl
  trans-compat-subst-one CC.`𝟙 T = refl
  trans-compat-subst-one (G₁ CC.`× G₂) T =
    cong₂ _`×_ (trans-compat-subst-one G₁ T) (trans-compat-subst-one G₂ T)
  trans-compat-subst-one (G₁ CC.`+ G₂) T =
    cong₂ _`+_ (trans-compat-subst-one G₁ T) (trans-compat-subst-one G₂ T)
  trans-compat-subst-one (CC.` zero) T = refl
  trans-compat-subst-one (CC.` (suc x)) T = refl
  trans-compat-subst-one (CC.ind G) T =
    cong ind
      (trans (trans-compat-subst G (CC.extˢ (CC.σ₀ T)))
        (cong (λ hole → sub hole T⟦ G ⟧)
          (extensionality (λ x → trans (trans-compat-ext (CC.σ₀ T) x)
            (cong (λ hole → extˢ hole x)
              (extensionality (trans-compat-lemma T)))))))

  trans-compat-subst0 : ∀ G T → T⟦ G CC.⇐ T ⟧ ≡ T⟦ G ⟧ ⇐ T⟦ T ⟧
  -- there should be a more direct proof along the lines of the case for `CC.ind G`
  -- trans-compat-subst0 G T = trans (trans-compat-subst G (CC.σ₀ T)) {!trans (cong sub!}
  trans-compat-subst0 CC.`𝟘 T = refl
  trans-compat-subst0 CC.`𝟙 T = refl
  trans-compat-subst0 (G₁ CC.`× G₂) T =
    cong₂ _`×_ (trans-compat-subst0 G₁ T) (trans-compat-subst0 G₂ T)
  trans-compat-subst0 (G₁ CC.`+ G₂) T =
    cong₂ _`+_ (trans-compat-subst0 G₁ T) (trans-compat-subst0 G₂ T)
  trans-compat-subst0 (CC.` zero) T = refl
  trans-compat-subst0 (CC.ind G) T = cong ind (trans-compat-ind G T)


  -- translation of types preserves meaning

  record _≅_ A B : Set where
    field
      from : A → B
      to   : B → A
      to∘from : ∀ (x : A) → to (from x) ≡ x
      from∘to : ∀ (y : B) → from (to y) ≡ y

  id-≅ : ∀ {A} → A ≅ A
  id-≅ = record { from = λ x → x ; to = λ y → y ; to∘from = λ x → refl ; from∘to = λ y → refl }
  open _≅_

  {-# TERMINATING #-}
  from-T : ∀ (T : CC.TY) → CC.⟦ T ⟧ᵀ → ⟦ T⟦ T ⟧ ⟧ᵀ
  to-T : ∀ (T : CC.TY) → ⟦ T⟦ T ⟧ ⟧ᵀ → CC.⟦ T ⟧ᵀ
  from-fmap : (G : CC.Ty 1) (H : CC.Ty 1)
    → (∀ T → CC.⟦ T ⟧ᵀ → ⟦ T⟦ T ⟧ ⟧ᵀ)
    → CC.⟦ G CC.⇐ CC.ind H ⟧ᵀ → ⟦ T⟦ G ⟧ ⇐ ind T⟦ H ⟧ ⟧ᵀ
  to-fmap : (G : CC.Ty 1) (H : CC.Ty 1)
    → (∀ T → ⟦ T⟦ T ⟧ ⟧ᵀ → CC.⟦ T ⟧ᵀ)
    → ⟦ T⟦ G ⟧ ⇐ ind T⟦ H ⟧ ⟧ᵀ → CC.⟦ G CC.⇐ CC.ind H ⟧ᵀ

  from-T CC.`𝟙 tt = tt
  from-T (T₁ CC.`× T₂) (x , y) = (from-T T₁ x) , (from-T T₂ y)
  from-T (T₁ CC.`+ T₂) (inj₁ x) = inj₁ (from-T T₁ x)
  from-T (T₁ CC.`+ T₂) (inj₂ y) = inj₂ (from-T T₂ y)
  from-T (CC.ind G) (CC.con x) = con (from-fmap G G from-T x)

  to-T CC.`𝟙 tt = tt
  to-T (T₁ CC.`× T₂) (x , y) = (to-T T₁ x) , (to-T T₂ y)
  to-T (T₁ CC.`+ T₂) (inj₁ x) = inj₁ (to-T T₁ x)
  to-T (T₁ CC.`+ T₂) (inj₂ y) = inj₂ (to-T T₂ y)
  to-T (CC.ind G) (con x) = CC.con (to-fmap G G to-T x)

  from-fmap G H f x =
    subst ⟦_⟧ᵀ (trans-compat-subst0 G (CC.ind H))
      (from-T (G CC.⇐ CC.ind H) x)

  to-fmap G H f x =
    to-T (G CC.⇐ CC.ind H)
      (subst ⟦_⟧ᵀ (sym (trans-compat-subst0 G (CC.ind H))) x)

  subst-cancel : ∀ {A B : TY} (p : A ≡ B) (x : ⟦ A ⟧ᵀ)
    → subst ⟦_⟧ᵀ (sym p) (subst ⟦_⟧ᵀ p x) ≡ x
  subst-cancel refl x = refl

  subst-cancel⁻¹ : ∀ {A B : TY} (p : A ≡ B) (y : ⟦ B ⟧ᵀ)
    → subst ⟦_⟧ᵀ p (subst ⟦_⟧ᵀ (sym p) y) ≡ y
  subst-cancel⁻¹ refl y = refl

  {-# TERMINATING #-}
  to∘from-T : ∀ (T : CC.TY) → ∀ x → to-T T (from-T T x) ≡ x
  to∘from-fmap-T : ∀ (G H : CC.Ty 1) → ∀ x
    → to-fmap G H to-T (from-fmap G H from-T x) ≡ x
  from∘to-T : ∀ (T : CC.TY) → ∀ x → from-T T (to-T T x) ≡ x
  from∘to-fmap-T : ∀ (G H : CC.Ty 1) → ∀ x
    → from-fmap G H from-T (to-fmap G H to-T x) ≡ x

  to∘from-T CC.`𝟘 ()
  to∘from-T CC.`𝟙 tt = refl
  to∘from-T (T₁ CC.`× T₂) (x , y) =
    cong₂ _,_ (to∘from-T T₁ x) (to∘from-T T₂ y)
  to∘from-T (T₁ CC.`+ T₂) (inj₁ x) = cong inj₁ (to∘from-T T₁ x)
  to∘from-T (T₁ CC.`+ T₂) (inj₂ y) = cong inj₂ (to∘from-T T₂ y)
  to∘from-T (CC.ind G) (CC.con x) = cong CC.con (to∘from-fmap-T G G x)

  to∘from-fmap-T G H x =
    trans
      (cong (to-T (G CC.⇐ CC.ind H))
        (subst-cancel (trans-compat-subst0 G (CC.ind H))
          (from-T (G CC.⇐ CC.ind H) x)))
      (to∘from-T (G CC.⇐ CC.ind H) x)

  from∘to-T CC.`𝟘 ()
  from∘to-T CC.`𝟙 tt = refl
  from∘to-T (T₁ CC.`× T₂) (x , y) =
    cong₂ _,_ (from∘to-T T₁ x) (from∘to-T T₂ y)
  from∘to-T (T₁ CC.`+ T₂) (inj₁ x) = cong inj₁ (from∘to-T T₁ x)
  from∘to-T (T₁ CC.`+ T₂) (inj₂ y) = cong inj₂ (from∘to-T T₂ y)
  from∘to-T (CC.ind G) (con x) = cong con (from∘to-fmap-T G G x)

  from∘to-fmap-T G H x =
    trans
      (cong (subst ⟦_⟧ᵀ (trans-compat-subst0 G (CC.ind H)))
        (from∘to-T (G CC.⇐ CC.ind H)
          (subst ⟦_⟧ᵀ (sym (trans-compat-subst0 G (CC.ind H))) x)))
      (subst-cancel⁻¹ (trans-compat-subst0 G (CC.ind H)) x)

  type-trans-preserves : ∀ (T : CC.TY) → CC.⟦ T ⟧ᵀ ≅ ⟦ T⟦ T ⟧ ⟧ᵀ
  type-trans-preserves T =
    record {
      from = from-T T ;
      to = to-T T ;
      to∘from = to∘from-T T ;
      from∘to = from∘to-T T }

  type-alg-preserves : ∀ (G : CC.Ty 1) → CC.Alg G ≅ Alg T⟦ G ⟧
  type-alg-preserves G = type-trans-preserves (CC.ind G)


  -- translation of arrows

  E⟦_⟧ : ∀ {T U : CC.TY} → T CC.→ᴾ U → T⟦ T ⟧ →ᴾ T⟦ U ⟧
  E⟦ CC.id ⟧ = id
  E⟦ CC.C p₁ p₂ ⟧ = C E⟦ p₁ ⟧ E⟦ p₂ ⟧
  E⟦ CC.`⊤ ⟧ = `⊤
  E⟦ CC.`⊥ ⟧ = `⊥
  E⟦ CC.`# p₁ p₂ ⟧ = `# E⟦ p₁ ⟧ E⟦ p₂ ⟧
  E⟦ CC.π₁ ⟧ = π₁
  E⟦ CC.π₂ ⟧ = π₂
  E⟦ CC.ι₁ ⟧ = ι₁
  E⟦ CC.ι₂ ⟧ = ι₂
  E⟦ CC.`case p₁ p₂ ⟧ = `case E⟦ p₁ ⟧ E⟦ p₂ ⟧
  E⟦ CC.dist-+-x ⟧ = dist-+-x
  E⟦ CC.con{G = G} ⟧
    rewrite trans-compat-subst0 G (CC.ind G) = con
  E⟦ CC.P{G = G}{T = T} p ⟧
    with E⟦ p ⟧
  ... | Ep
    rewrite trans-compat-subst0 G (T CC.`× CC.ind G) = P Ep
  E⟦ CC.F{G = G}{T = T} p ⟧
    with E⟦ p ⟧
  ... | Ep
    rewrite trans-compat-subst0 G T = F Ep

  -- translation preserves semantics

  eq-unfoldᵀ : ∀ (τ : Sub 1 0) (H : Ty 2)
    → sub τ (sub (σ₀ (ind H)) H)
      ≡ sub (extˢ τ) H ⇐ ind (sub (extˢ τ) H)
  eq-unfoldᵀ τ H = begin
       sub τ (sub (σ₀ (ind H)) H)
    ≡⟨ sub-sub (σ₀ (ind H)) τ H ⟩
       sub (σ₀ (ind H) ˢ⨟ˢ τ) H
    ≡⟨ sub~ {t = H} (comm-⨟-σ₀ τ (ind H)) ⟩
       sub (extˢ τ ˢ⨟ˢ σ₀ (sub τ (ind H))) H
    ≡⟨ sym (sub-sub (extˢ τ) (σ₀ (sub τ (ind H))) H) ⟩
       sub (extˢ τ) H ⇐ ind (sub (extˢ τ) H)
    ∎

  subst-ind : ∀ {G H : Ty 1} (p : G ≡ H)
    (x : ⟦ G ⇐ ind G ⟧ᵀ)
    → subst ⟦_⟧ᵀ (cong ind p) (con x)
      ≡ con (subst ⟦_⟧ᵀ (cong (λ K → K ⇐ ind K) p) x)
  subst-ind refl x = refl

  from-T-subst : ∀ {A B : CC.TY} (p : A ≡ B) (x : CC.⟦ A ⟧ᵀ)
    → from-T B (subst CC.⟦_⟧ᵀ p x)
      ≡ subst ⟦_⟧ᵀ (cong T⟦_⟧ p) (from-T A x)
  from-T-subst refl x = refl

  subst-coherence : ∀ {A B C : TY}
    (p : A ≡ B) (q : B ≡ C) (r : A ≡ C) (x : ⟦ A ⟧ᵀ)
    → subst ⟦_⟧ᵀ q (subst ⟦_⟧ᵀ p x) ≡ subst ⟦_⟧ᵀ r x
  subst-coherence refl refl refl x = refl

  subst₃-coherence : ∀ {A B C D E F : TY}
    (p₁ : A ≡ B) (p₂ : B ≡ C) (p₃ : C ≡ D)
    (q₁ : A ≡ E) (q₂ : E ≡ F) (q₃ : F ≡ D)
    (x : ⟦ A ⟧ᵀ)
    → subst ⟦_⟧ᵀ p₃ (subst ⟦_⟧ᵀ p₂ (subst ⟦_⟧ᵀ p₁ x))
      ≡ subst ⟦_⟧ᵀ q₃ (subst ⟦_⟧ᵀ q₂ (subst ⟦_⟧ᵀ q₁ x))
  subst₃-coherence refl refl refl refl refl refl x = refl

  fmap-type-coherence : ∀ {A B : Ty 1} (p : A ≡ B)
    {S T : TY} (f : ⟦ S ⟧ᵀ → ⟦ T ⟧ᵀ) (x : ⟦ A ⇐ S ⟧ᵀ)
    → subst ⟦_⟧ᵀ (cong (λ K → K ⇐ T) p) (fmap A f x)
      ≡ fmap B f (subst ⟦_⟧ᵀ (cong (λ K → K ⇐ S) p) x)
  fmap-type-coherence refl f x = refl

  CC-fmap-ind : ∀ {S T : CC.TY} (G : CC.Ty 2)
    (f : CC.⟦ S ⟧ᵀ → CC.⟦ T ⟧ᵀ)
    (x : CC.⟦ CC.sub (CC.extˢ (CC.σ₀ S)) G
              CC.⇐ CC.ind (CC.sub (CC.extˢ (CC.σ₀ S)) G) ⟧ᵀ)
    → CC.fmap (CC.ind G) f (CC.con x)
      ≡ CC.con
          (subst CC.⟦_⟧ᵀ (CC.eq-unfold (CC.σ₀ T) G)
            (CC.fmap (G CC.⇐ CC.ind G) f
              (subst CC.⟦_⟧ᵀ (sym (CC.eq-unfold (CC.σ₀ S) G)) x)))
  CC-fmap-ind {S} {T} G f x
    rewrite sym (CC.eq-unfold (CC.σ₀ S) G)
    with CC.fmap (G CC.⇐ CC.ind G) f x
  ... | ih rewrite CC.eq-unfold (CC.σ₀ T) G = refl

  fmap-ind : ∀ {S T : TY} (G : Ty 2)
    (f : ⟦ S ⟧ᵀ → ⟦ T ⟧ᵀ)
    (x : ⟦ sub (extˢ (σ₀ S)) G ⇐ ind (sub (extˢ (σ₀ S)) G) ⟧ᵀ)
    → fmap (ind G) f (con x)
      ≡ con
          (subst ⟦_⟧ᵀ (eq-unfoldᵀ (σ₀ T) G)
            (fmap (sub (σ₀ (ind G)) G) f
              (subst ⟦_⟧ᵀ (sym (eq-unfoldᵀ (σ₀ S) G)) x)))
  fmap-ind {S} {T} G f x
    rewrite sym (eq-unfoldᵀ (σ₀ S) G)
    with fmap (sub (σ₀ (ind G)) G) f x
  ... | ih rewrite eq-unfoldᵀ (σ₀ T) G = refl

  subst-× : ∀ {A A′ B B′ : TY} (p : A ≡ A′) (q : B ≡ B′)
    (x : ⟦ A ⟧ᵀ) (y : ⟦ B ⟧ᵀ)
    → subst ⟦_⟧ᵀ (cong₂ _`×_ p q) (x , y)
      ≡ (subst ⟦_⟧ᵀ p x , subst ⟦_⟧ᵀ q y)
  subst-× refl refl x y = refl

  subst-+₁ : ∀ {A A′ B B′ : TY} (p : A ≡ A′) (q : B ≡ B′)
    (x : ⟦ A ⟧ᵀ)
    → subst ⟦_⟧ᵀ (cong₂ _`+_ p q) (inj₁ x)
      ≡ inj₁ (subst ⟦_⟧ᵀ p x)
  subst-+₁ refl refl x = refl

  subst-+₂ : ∀ {A A′ B B′ : TY} (p : A ≡ A′) (q : B ≡ B′)
    (y : ⟦ B ⟧ᵀ)
    → subst ⟦_⟧ᵀ (cong₂ _`+_ p q) (inj₂ y)
      ≡ inj₂ (subst ⟦_⟧ᵀ q y)
  subst-+₂ refl refl y = refl

  {-# TERMINATING #-}
  from-fmap-natural : ∀ {S T : CC.TY} (G : CC.Ty 1)
    {f : CC.⟦ S ⟧ᵀ → CC.⟦ T ⟧ᵀ}
    {f′ : ⟦ T⟦ S ⟧ ⟧ᵀ → ⟦ T⟦ T ⟧ ⟧ᵀ}
    → (∀ x → from-T T (f x) ≡ f′ (from-T S x))
    → ∀ x
    → subst ⟦_⟧ᵀ (trans-compat-subst0 G T)
        (from-T (G CC.⇐ T) (CC.fmap G f x))
      ≡ fmap T⟦ G ⟧ f′
          (subst ⟦_⟧ᵀ (trans-compat-subst0 G S)
            (from-T (G CC.⇐ S) x))
  from-fmap-natural CC.`𝟘 h ()
  from-fmap-natural CC.`𝟙 h tt = refl
  from-fmap-natural {S} {T} (G CC.`× H) {f} {f′} h (x , y)
    rewrite subst-× (trans-compat-subst0 G T) (trans-compat-subst0 H T)
                    (from-T (G CC.⇐ T) (CC.fmap G f x))
                    (from-T (H CC.⇐ T) (CC.fmap H f y))
          | subst-× (trans-compat-subst0 G S) (trans-compat-subst0 H S)
                    (from-T (G CC.⇐ S) x) (from-T (H CC.⇐ S) y)
          | from-fmap-natural G h x | from-fmap-natural H h y = refl
  from-fmap-natural {S} {T} (G CC.`+ H) {f} {f′} h (inj₁ x)
    rewrite subst-+₁ (trans-compat-subst0 G T) (trans-compat-subst0 H T)
                    (from-T (G CC.⇐ T) (CC.fmap G f x))
          | subst-+₁ (trans-compat-subst0 G S) (trans-compat-subst0 H S)
                    (from-T (G CC.⇐ S) x)
          | from-fmap-natural G h x = refl
  from-fmap-natural {S} {T} (G CC.`+ H) {f} {f′} h (inj₂ y)
    rewrite subst-+₂ (trans-compat-subst0 G T) (trans-compat-subst0 H T)
                    (from-T (H CC.⇐ T) (CC.fmap H f y))
          | subst-+₂ (trans-compat-subst0 G S) (trans-compat-subst0 H S)
                    (from-T (H CC.⇐ S) y)
          | from-fmap-natural H h y = refl
  from-fmap-natural (CC.` zero) h x = h x
  from-fmap-natural {S} {T} (CC.ind G) {f} {f′} h (CC.con x)
    = begin
      subst ⟦_⟧ᵀ (cong ind (trans-compat-ind G T))
        (from-T (CC.ind (CC.sub (CC.extˢ (CC.σ₀ T)) G))
          (CC.fmap (CC.ind G) f (CC.con x)))
    ≡⟨ cong
         (λ z → subst ⟦_⟧ᵀ (cong ind (trans-compat-ind G T))
           (from-T (CC.ind (CC.sub (CC.extˢ (CC.σ₀ T)) G)) z))
         (CC-fmap-ind G f x) ⟩
      subst ⟦_⟧ᵀ (cong ind (trans-compat-ind G T))
        (from-T (CC.ind (CC.sub (CC.extˢ (CC.σ₀ T)) G))
          (CC.con
            (subst CC.⟦_⟧ᵀ (CC.eq-unfold (CC.σ₀ T) G)
              (CC.fmap (G CC.⇐ CC.ind G) f
                (subst CC.⟦_⟧ᵀ (sym (CC.eq-unfold (CC.σ₀ S) G)) x)))))
    ≡⟨ subst-ind (trans-compat-ind G T) _ ⟩
      con
        (subst ⟦_⟧ᵀ
          (cong (λ K → K ⇐ ind K) (trans-compat-ind G T))
          (subst ⟦_⟧ᵀ
            (trans-compat-subst0
              (CC.sub (CC.extˢ (CC.σ₀ T)) G)
              (CC.ind (CC.sub (CC.extˢ (CC.σ₀ T)) G)))
            (from-T
              (CC.sub (CC.extˢ (CC.σ₀ T)) G CC.⇐
                CC.ind (CC.sub (CC.extˢ (CC.σ₀ T)) G))
              (subst CC.⟦_⟧ᵀ (CC.eq-unfold (CC.σ₀ T) G)
                (CC.fmap (G CC.⇐ CC.ind G) f
                  (subst CC.⟦_⟧ᵀ (sym (CC.eq-unfold (CC.σ₀ S) G)) x))))))
    ≡⟨ cong con
         (let G₀ = G CC.⇐ CC.ind G
              G₀ᵀ = sub (σ₀ (ind T⟦ G ⟧)) T⟦ G ⟧
              Hₛ = CC.sub (CC.extˢ (CC.σ₀ S)) G
              Hₜ = CC.sub (CC.extˢ (CC.σ₀ T)) G
              Hₛᵀ = sub (extˢ (σ₀ T⟦ S ⟧)) T⟦ G ⟧
              Hₜᵀ = sub (extˢ (σ₀ T⟦ T ⟧)) T⟦ G ⟧
              eₛ = CC.eq-unfold (CC.σ₀ S) G
              eₜ = CC.eq-unfold (CC.σ₀ T) G
              eₛᵀ = eq-unfoldᵀ (σ₀ T⟦ S ⟧) T⟦ G ⟧
              eₜᵀ = eq-unfoldᵀ (σ₀ T⟦ T ⟧) T⟦ G ⟧
              a = trans-compat-subst-one G (CC.ind G)
              qₛ = trans-compat-subst0 Hₛ (CC.ind Hₛ)
              qₜ = trans-compat-subst0 Hₜ (CC.ind Hₜ)
              q₀ₛ = trans-compat-subst0 G₀ S
              q₀ₜ = trans-compat-subst0 G₀ T
              rₛ = cong (λ K → K ⇐ ind K) (trans-compat-ind G S)
              rₜ = cong (λ K → K ⇐ ind K) (trans-compat-ind G T)
              aₛ = cong (λ K → K ⇐ T⟦ S ⟧) a
              aₜ = cong (λ K → K ⇐ T⟦ T ⟧) a
              xₛ = subst CC.⟦_⟧ᵀ (sym eₛ) x
              yₜ = CC.fmap G₀ f xₛ
              zₛ = subst ⟦_⟧ᵀ rₛ
                     (subst ⟦_⟧ᵀ qₛ (from-T (Hₛ CC.⇐ CC.ind Hₛ) x))
          in begin
            subst ⟦_⟧ᵀ rₜ
              (subst ⟦_⟧ᵀ qₜ
                (from-T (Hₜ CC.⇐ CC.ind Hₜ) (subst CC.⟦_⟧ᵀ eₜ yₜ)))
          ≡⟨ cong (λ z → subst ⟦_⟧ᵀ rₜ (subst ⟦_⟧ᵀ qₜ z))
               (from-T-subst eₜ yₜ) ⟩
            subst ⟦_⟧ᵀ rₜ
              (subst ⟦_⟧ᵀ qₜ
                (subst ⟦_⟧ᵀ (cong T⟦_⟧ eₜ)
                  (from-T (G₀ CC.⇐ T) yₜ)))
          ≡⟨ subst₃-coherence (cong T⟦_⟧ eₜ) qₜ rₜ q₀ₜ aₜ eₜᵀ
               (from-T (G₀ CC.⇐ T) yₜ) ⟩
            subst ⟦_⟧ᵀ eₜᵀ
              (subst ⟦_⟧ᵀ aₜ
                (subst ⟦_⟧ᵀ q₀ₜ (from-T (G₀ CC.⇐ T) yₜ)))
          ≡⟨ cong (λ z → subst ⟦_⟧ᵀ eₜᵀ (subst ⟦_⟧ᵀ aₜ z))
               (from-fmap-natural G₀ h xₛ) ⟩
            subst ⟦_⟧ᵀ eₜᵀ
              (subst ⟦_⟧ᵀ aₜ
                (fmap T⟦ G₀ ⟧ f′
                  (subst ⟦_⟧ᵀ q₀ₛ (from-T (G₀ CC.⇐ S) xₛ))))
          ≡⟨ cong (subst ⟦_⟧ᵀ eₜᵀ)
               (fmap-type-coherence a f′
                 (subst ⟦_⟧ᵀ q₀ₛ (from-T (G₀ CC.⇐ S) xₛ))) ⟩
            subst ⟦_⟧ᵀ eₜᵀ
              (fmap G₀ᵀ f′
                (subst ⟦_⟧ᵀ aₛ
                  (subst ⟦_⟧ᵀ q₀ₛ (from-T (G₀ CC.⇐ S) xₛ))))
          ≡⟨ cong (λ z → subst ⟦_⟧ᵀ eₜᵀ (fmap G₀ᵀ f′ z))
               (begin
                  subst ⟦_⟧ᵀ aₛ
                    (subst ⟦_⟧ᵀ q₀ₛ (from-T (G₀ CC.⇐ S) xₛ))
                ≡⟨ cong (λ z → subst ⟦_⟧ᵀ aₛ (subst ⟦_⟧ᵀ q₀ₛ z))
                     (from-T-subst (sym eₛ) x) ⟩
                  subst ⟦_⟧ᵀ aₛ
                    (subst ⟦_⟧ᵀ q₀ₛ
                      (subst ⟦_⟧ᵀ (cong T⟦_⟧ (sym eₛ))
                        (from-T (Hₛ CC.⇐ CC.ind Hₛ) x)))
                ≡⟨ subst₃-coherence (cong T⟦_⟧ (sym eₛ)) q₀ₛ aₛ
                     qₛ rₛ (sym eₛᵀ) (from-T (Hₛ CC.⇐ CC.ind Hₛ) x) ⟩
                  subst ⟦_⟧ᵀ (sym eₛᵀ) zₛ
                ∎) ⟩
            subst ⟦_⟧ᵀ eₜᵀ
              (fmap G₀ᵀ f′ (subst ⟦_⟧ᵀ (sym eₛᵀ) zₛ))
          ∎) ⟩
      con
        (subst ⟦_⟧ᵀ (eq-unfoldᵀ (σ₀ T⟦ T ⟧) T⟦ G ⟧)
          (fmap (sub (σ₀ (ind T⟦ G ⟧)) T⟦ G ⟧) f′
            (subst ⟦_⟧ᵀ (sym (eq-unfoldᵀ (σ₀ T⟦ S ⟧) T⟦ G ⟧))
              (subst ⟦_⟧ᵀ
                (cong (λ K → K ⇐ ind K) (trans-compat-ind G S))
                (subst ⟦_⟧ᵀ
                  (trans-compat-subst0
                    (CC.sub (CC.extˢ (CC.σ₀ S)) G)
                    (CC.ind (CC.sub (CC.extˢ (CC.σ₀ S)) G)))
                  (from-T
                    (CC.sub (CC.extˢ (CC.σ₀ S)) G CC.⇐
                      CC.ind (CC.sub (CC.extˢ (CC.σ₀ S)) G)) x))))))
    ≡⟨ sym (fmap-ind T⟦ G ⟧ f′ _) ⟩
      fmap (ind T⟦ G ⟧) f′
        (con
          (subst ⟦_⟧ᵀ
            (cong (λ K → K ⇐ ind K) (trans-compat-ind G S))
            (subst ⟦_⟧ᵀ
              (trans-compat-subst0
                (CC.sub (CC.extˢ (CC.σ₀ S)) G)
                (CC.ind (CC.sub (CC.extˢ (CC.σ₀ S)) G)))
              (from-T
                (CC.sub (CC.extˢ (CC.σ₀ S)) G CC.⇐
                  CC.ind (CC.sub (CC.extˢ (CC.σ₀ S)) G)) x))))
    ≡⟨ cong (fmap (ind T⟦ G ⟧) f′)
         (sym (subst-ind (trans-compat-ind G S) _)) ⟩
      fmap (ind T⟦ G ⟧) f′
        (subst ⟦_⟧ᵀ (cong ind (trans-compat-ind G S))
          (from-T (CC.ind (CC.sub (CC.extˢ (CC.σ₀ S)) G)) (CC.con x)))
    ∎

  eval-E-con : ∀ {G : CC.Ty 1}
    (x : ⟦ T⟦ G CC.⇐ CC.ind G ⟧ ⟧ᵀ)
    → eval E⟦ CC.con {G = G} ⟧ x
      ≡ con (subst ⟦_⟧ᵀ (trans-compat-subst0 G (CC.ind G)) x)
  eval-E-con {G} x rewrite trans-compat-subst0 G (CC.ind G) = refl

  unsubst : ∀ {A B : TY} (p : A ≡ B) {x : ⟦ A ⟧ᵀ} {y : ⟦ B ⟧ᵀ}
    → subst ⟦_⟧ᵀ p x ≡ y → x ≡ subst ⟦_⟧ᵀ (sym p) y
  unsubst p {x} e = trans (sym (subst-cancel p x)) (cong (subst ⟦_⟧ᵀ (sym p)) e)

  eval-E-P : ∀ {G : CC.Ty 1} {T U : CC.TY}
    (p : (G CC.⇐ (T CC.`× CC.ind G)) CC.`× U CC.→ᴾ T)
    (x : ⟦ T⟦ G ⟧ ⇐ ind T⟦ G ⟧ ⟧ᵀ) (u : ⟦ T⟦ U ⟧ ⟧ᵀ)
    → eval E⟦ CC.P {G = G} {T = T} {U = U} p ⟧ (con x , u)
      ≡ eval E⟦ p ⟧
          (subst ⟦_⟧ᵀ (sym (trans-compat-subst0 G (T CC.`× CC.ind G)))
            (fmap T⟦ G ⟧
              (λ v → eval E⟦ CC.P {G = G} {T = T} {U = U} p ⟧ (v , u) , v) x) , u)
  eval-E-P {G} {T} p x u with E⟦ p ⟧
  ... | Ep rewrite trans-compat-subst0 G (T CC.`× CC.ind G) = refl

  eval-E-F : ∀ {G : CC.Ty 1} {T U : CC.TY}
    (p : (G CC.⇐ T) CC.`× U CC.→ᴾ T)
    (x : ⟦ T⟦ G ⟧ ⇐ ind T⟦ G ⟧ ⟧ᵀ) (u : ⟦ T⟦ U ⟧ ⟧ᵀ)
    → eval E⟦ CC.F {G = G} {T = T} {U = U} p ⟧ (con x , u)
      ≡ eval E⟦ p ⟧
          (subst ⟦_⟧ᵀ (sym (trans-compat-subst0 G T))
            (fmap T⟦ G ⟧
              (λ v → eval E⟦ CC.F {G = G} {T = T} {U = U} p ⟧ (v , u)) x) , u)
  eval-E-F {G} {T} p x u with E⟦ p ⟧
  ... | Ep rewrite trans-compat-subst0 G T = refl

  {-# TERMINATING #-}
  trans-preserves-hard : ∀ {T U : CC.TY} → (p : T CC.→ᴾ U)
    → let T-≅ = type-trans-preserves T in
      let U-≅ = type-trans-preserves U in
      ∀ x → from U-≅ (CC.eval p x) ≡ eval E⟦ p ⟧ (from T-≅ x)
  trans-preserves-hard CC.id x = refl
  trans-preserves-hard (CC.C p₁ p₂) x
    rewrite trans-preserves-hard p₁ (CC.eval p₂ x)
          | trans-preserves-hard p₂ x = refl
  trans-preserves-hard CC.`⊤ x = refl
  trans-preserves-hard CC.`⊥ ()
  trans-preserves-hard (CC.`# p₁ p₂) x
    rewrite trans-preserves-hard p₁ x
          | trans-preserves-hard p₂ x = refl
  trans-preserves-hard CC.π₁ x = refl
  trans-preserves-hard CC.π₂ x = refl
  trans-preserves-hard CC.ι₁ x = refl
  trans-preserves-hard CC.ι₂ x = refl
  trans-preserves-hard (CC.`case p₁ p₂) (inj₁ x) = trans-preserves-hard p₁ x
  trans-preserves-hard (CC.`case p₁ p₂) (inj₂ y) = trans-preserves-hard p₂ y
  trans-preserves-hard CC.dist-+-x (inj₁ x , z) = refl
  trans-preserves-hard CC.dist-+-x (inj₂ y , z) = refl
  trans-preserves-hard (CC.con {G = G}) x =
    sym (eval-E-con (from-T (G CC.⇐ CC.ind G) x))
  trans-preserves-hard (CC.P {G = G} {T = T} {U = U} p) (CC.con x , u)
    = trans
        (trans-preserves-hard p
          (CC.fmap G (λ v → CC.eval (CC.P {G = G} {T = T} {U = U} p) (v , u) , v) x , u))
        (trans
          (cong (λ z → eval E⟦ p ⟧ (z , from-T U u))
            (unsubst (trans-compat-subst0 G (T CC.`× CC.ind G))
              (from-fmap-natural G
                {f = λ v → CC.eval (CC.P {G = G} {T = T} {U = U} p) (v , u) , v}
                {f′ = λ v → eval E⟦ CC.P {G = G} {T = T} {U = U} p ⟧
                                  (v , from-T U u) , v}
                (λ v → cong₂ _,_
                  (trans-preserves-hard (CC.P {G = G} {T = T} {U = U} p) (v , u)) refl) x)))
          (sym (eval-E-P {G = G} {T = T} {U = U} p
            (subst ⟦_⟧ᵀ (trans-compat-subst0 G (CC.ind G))
              (from-T (G CC.⇐ CC.ind G) x))
            (from-T U u))))
  trans-preserves-hard (CC.F {G = G} {T = T} {U = U} p) (CC.con x , u)
    = trans
        (trans-preserves-hard p
          (CC.fmap G (λ v → CC.eval (CC.F {G = G} {T = T} {U = U} p) (v , u)) x , u))
        (trans
          (cong (λ z → eval E⟦ p ⟧ (z , from-T U u))
            (unsubst (trans-compat-subst0 G T)
              (from-fmap-natural G
                {f = λ v → CC.eval (CC.F {G = G} {T = T} {U = U} p) (v , u)}
                {f′ = λ v → eval E⟦ CC.F {G = G} {T = T} {U = U} p ⟧
                                  (v , from-T U u)}
                (λ v → trans-preserves-hard
                  (CC.F {G = G} {T = T} {U = U} p) (v , u)) x)))
          (sym (eval-E-F {G = G} {T = T} {U = U} p
            (subst ⟦_⟧ᵀ (trans-compat-subst0 G (CC.ind G))
              (from-T (G CC.⇐ CC.ind G) x))
            (from-T U u))))

  trans-preserves : ∀ {T U : CC.TY} → (p : T CC.→ᴾ U)
    → let T-≅ = type-trans-preserves T in
      let U-≅ = type-trans-preserves U in
    ∀ x → from U-≅ (CC.eval p x) ≡ eval E⟦ p ⟧ (from T-≅ x)
  trans-preserves CC.id x = refl
  trans-preserves (CC.C p₁ p₂) x
    rewrite trans-preserves p₁ (CC.eval p₂ x)
          | trans-preserves p₂ x = refl
  trans-preserves CC.`⊤ x = refl
  trans-preserves CC.`⊥ ()
  trans-preserves (CC.`# p₁ p₂) x
    rewrite trans-preserves p₁ x
          | trans-preserves p₂ x = refl
  trans-preserves CC.π₁ x = refl
  trans-preserves CC.π₂ x = refl
  trans-preserves CC.ι₁ x = refl
  trans-preserves CC.ι₂ x = refl
  trans-preserves (CC.`case p₁ p₂) (inj₁ x) = trans-preserves p₁ x
  trans-preserves (CC.`case p₁ p₂) (inj₂ y) = trans-preserves p₂ y
  trans-preserves CC.dist-+-x x = trans-preserves-hard CC.dist-+-x x
  trans-preserves CC.con x = trans-preserves-hard CC.con x
  trans-preserves (CC.P p) x = trans-preserves-hard (CC.P p) x
  trans-preserves (CC.F p) x = trans-preserves-hard (CC.F p) x

\end{code}
