\begin{code}
{-# OPTIONS --large-indices #-}
module PrimRecWord where

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Binary.PropositionalEquality.WithK using (≡-irrelevant)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟨; step-≡-⟩; _∎)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; suc; zero; _*_; _+_)
open import Data.Fin using (Fin; suc; zero)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head)
open import Data.Vec.Properties using (lookup-map)
open import Data.List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_; _++_ to _++ᴸ_; length to lengthᴸ; map to mapᴸ)
open import Function using (_∘_)

open import Utils

----------------------------------------------------------------------
-- primitive recursion on ℕ
----------------------------------------------------------------------

import PR-Nat as Nats

----------------------------------------------------------------------
-- vector-valued pr on ℕ
-- PR m n encodes functions ℕᵐ → ℕⁿ
----------------------------------------------------------------------

import PR-NatsVec as NatsVec

module Nats-NatsVec where

  open Nats
  open NatsVec

  {-# TERMINATING #-}
  ⟦_⟧ : Nats.PR m → NatsVec.PR m 1
  ⟦_⟧* : Vec (Nats.PR m) n → NatsVec.PR m n

  ⟦ Z ⟧ = C PR.Z `0
  ⟦ σ ⟧ = PR.σ
  ⟦ π i ⟧ = π i
  ⟦ C g f* ⟧ = PR.C ⟦ g ⟧ ⟦ f* ⟧*
  ⟦ P g h ⟧ = PR.P ⟦ g ⟧ ⟦ h ⟧
  ⟦ F g h ⟧ = ⟦ F⇒P g h ⟧

  ⟦ [] ⟧* = `0
  ⟦ f ∷ f* ⟧* = ♯ ⟦ f ⟧ ⟦ f* ⟧*

  {-# TERMINATING #-}
  sound : (p : Nats.PR m) (v* : Vec ℕ m) → ∀ {r : Vec ℕ o} → Nats.eval p v* ∷ r ≡ NatsVec.eval ⟦ p ⟧ v* ++ r
  sound* : (f* : Vec (Nats.PR m) n) (v* : Vec ℕ m) → Nats.eval* f* v* ≡ NatsVec.eval ⟦ f* ⟧* v*

  sound Z [] = refl
  sound σ (x ∷ []) = refl
  sound (π i) v* = refl
  sound (C g f*) v* rewrite sound* f* v* = sound g (NatsVec.eval ⟦ f* ⟧* v*)
  sound (P g h) (zero ∷ v*) = sound g v*
  sound (P g h) (suc x ∷ v*) rewrite sound (P g h) (x ∷ v*) {x ∷ v*} = sound h (NatsVec.eval (P ⟦ g ⟧ ⟦ h ⟧) (x ∷ v*) ++ x ∷ v*) 
  sound (F g h) v* = trans (cong (_∷ _) (F⇒P-sound g h v*)) (sound (F⇒P g h) v*)

  sound* [] v* = refl
  sound* (f ∷ f*) v* rewrite sound* f* v* =  sound f v* {NatsVec.eval ⟦ f* ⟧* v*}

----------------------------------------------------------------------
-- primitive recursion on words over alphabet A
----------------------------------------------------------------------

import PR-Words as Words

----------------------------------------------------------------------
-- primitive recursion on trees over ranked alphabet A
----------------------------------------------------------------------

{- obsolete -}
module Trees where

  Rank : Set → Set
  Rank A = A → ℕ

  data PRR (r : Rank A) : ℕ → Set where
    σ : (a : A) → PRR r (r a)
    π : (i : Fin n) → PRR r n
    C : PRR r m → Vec (PRR r n) m → PRR r n
    P : (h : (a : A) → PRR r (r a + r a + n)) → PRR r (suc n)
  
  data Alg (r : Rank A) : Set where
    con : (a : A) → Vec (Alg r) (r a) → Alg r

  {-# TERMINATING #-}
  eval  : ∀ {r : Rank A} → PRR r n → Vec (Alg r) n → Alg r
  eval* : ∀ {r : Rank A} → Vec (PRR r n) m → Vec (Alg r) n → Vec (Alg r) m

  eval (σ a) v* = con a v*
  eval (π i) v* = lookup v* i
  eval (C f g*) v* = eval f (eval* g* v*)
  eval {r = r} (P h) (con a xs ∷ v*) = eval (h a) ((map (λ x → eval (P h) (x ∷ v*)) xs ++ xs) ++ v* )

  eval* [] v* = []
  eval* (x ∷ p*) v* = (eval x v*) ∷ (eval* p* v*)

----------------------------------------------------------------------
-- primitive recursion on trees over S-sorted alphabet A
----------------------------------------------------------------------

module HTrees where

  data HVec (F : S → Set) : ∀ {n} → Vec S n → Set where
    []ᴴ  : HVec F []
    _∷ᴴ_ : ∀ {n s ss} → F s → HVec F {n} ss → HVec F (s ∷ ss)

  hlookup : ∀ {ss : Vec S n}{F : S → Set} (a* : HVec F ss) → (i : Fin n) → F (lookup ss i)
  hlookup {ss = s ∷ ss} (a ∷ᴴ a*) Fin.zero = a
  hlookup {ss = s ∷ ss} (a ∷ᴴ a*) (Fin.suc i) = hlookup a* i

  _++ᴴ_ : ∀ {F : S → Set}{n₁ n₂}{ss₁ : Vec S n₁}{ss₂ : Vec S n₂} → HVec F ss₁ → HVec F ss₂ → HVec F (ss₁ ++ ss₂)
  []ᴴ ++ᴴ ys = ys
  (x ∷ᴴ xs) ++ᴴ ys = x ∷ᴴ (xs ++ᴴ ys)

  mapᴴ : ∀ {F : S → Set}{n}{ss : Vec S n} {res : S → S} → (∀ {s} → F s → F (res s)) → HVec F ss → HVec F (map res ss)
  mapᴴ f []ᴴ = []ᴴ
  mapᴴ f (x ∷ᴴ a*) = f x ∷ᴴ mapᴴ f a*

  toHVec : {S : Set} (v : Vec S n) → HVec (λ x → S) v
  toHVec [] = []ᴴ
  toHVec (x ∷ v) = x ∷ᴴ toHVec v

  ----------------------------------------------------------------------

  Rank : Set → Set
  Rank A = A → ℕ

  HRank : Set → (A : Set) → (Rank A) → Set
  HRank S A r = (a : A) → Vec S (r a) × S

  data Alg {r : Rank A} (hr : HRank S A r) : S → Set where
    con : (a : A) → HVec (Alg hr) (proj₁ (hr a)) → Alg hr (proj₂ (hr a))

  {-# NO_POSITIVITY_CHECK #-}
  data PR {r} (hr : HRank S A r) : (n : ℕ) → Vec S n × S → Set where
    σ : (a : A) → PR hr (r a) (hr a)
    π : ∀ {ss : Vec S n} → (i : Fin n) → PR hr n ⟨ ss , lookup ss i ⟩
    C : ∀ {s m} {ss′ : Vec S m} {ss : Vec S n}
      → PR hr n ⟨ ss , s ⟩
      → HVec (λ s → PR hr m ⟨ ss′ , s ⟩) ss
      → PR hr m ⟨ ss′ , s ⟩
    P : ∀ {s₀}{n}{ss : Vec S n}
      → (res : S → S)
      → (h : (s : S) (a : A) → proj₂ (hr a) ≡ s → PR hr ((r a + r a) + n) ⟨ (map res (proj₁ (hr a)) ++ (proj₁ (hr a))) ++ ss , res s ⟩)
      → PR hr (suc n) ⟨ s₀ ∷ ss , res s₀ ⟩

  {-# TERMINATING #-}
  eval : ∀ {r : Rank A}{hr : HRank S A r} {n} {s* : Vec S n} {s} → PR hr n ⟨ s* , s ⟩ → HVec (Alg hr) s* → Alg hr s
  eval* : ∀ {r : Rank A}{hr : HRank S A r} {n} {s* : Vec S n} {m} {ss : Vec S m} → HVec (λ s → PR hr n ⟨ s* , s ⟩) ss → HVec (Alg hr) s* → HVec (Alg hr) ss

  eval (σ a) v* = con a v*
  eval (π i) v* = hlookup v* i
  eval (C f g*) v* = eval f (eval* g* v*)
  eval (P {s₀ = s₀} res h) (con a x* ∷ᴴ v*) = eval (h s₀ a refl) ((mapᴴ (λ {s} → λ x → eval (P{s₀ = s} res h) (x ∷ᴴ v*)) x* ++ᴴ x*) ++ᴴ v*)

  eval* []ᴴ v* = []ᴴ
  eval* (p ∷ᴴ p*) v* = eval p v* ∷ᴴ eval* p* v*


module HTrees2 where

  data HVec : ∀ {n} → Vec Set n → Set where
    []ᴴ  : HVec []
    _∷ᴴ_ : ∀ {n A}{V : Vec Set n} → A → HVec V → HVec (A ∷ V)

  hlookup : ∀ {ss : Vec Set n} (a* : HVec ss) → (i : Fin n) → lookup ss i
  hlookup {ss = s ∷ ss} (a ∷ᴴ a*) Fin.zero = a
  hlookup {ss = s ∷ ss} (a ∷ᴴ a*) (Fin.suc i) = hlookup a* i

  _++ᴴ_ : ∀{n₁ n₂}{ss₁ : Vec Set n₁}{ss₂ : Vec Set n₂} → HVec ss₁ → HVec ss₂ → HVec (ss₁ ++ ss₂)
  []ᴴ ++ᴴ ys = ys
  (x ∷ᴴ xs) ++ᴴ ys = x ∷ᴴ (xs ++ᴴ ys)

  mapᴴ : ∀{n}{ss rss : Vec Set n} → (∀ {i : Fin n} → lookup ss i → lookup rss i) → HVec ss → HVec rss
  mapᴴ{rss = []} f []ᴴ = []ᴴ
  mapᴴ{rss = A ∷ V} f (a ∷ᴴ a*) = f {zero} a ∷ᴴ mapᴴ (λ{i} → f{suc i}) a*

  toHVec : (v : Vec S n) → HVec (repeat n S)
  toHVec [] = []ᴴ
  toHVec (x ∷ x*) = x ∷ᴴ toHVec x*

  Rank : Set → Set
  Rank A = A → ℕ

  HRank : Set → (A : Set) → (Rank A) → Set
  HRank S A r = (a : A) → Vec S (r a) × S

  -- unfortunately, this definition is not strictly positive!
  module not-strictly-positive where
    -- data Alg {r : Rank A} (hr : HRank S A r) : S → Set where
    --   con : (a : A) → HVec (map (Alg hr) (proj₁ (hr a))) → Alg hr (proj₂ (hr a))

    

    -- data PR {r} (hr : HRank S A r) : (n : ℕ) → Vec S n × S → Set where
    --   σ : (a : A) → PR hr (r a) (hr a)
    --   π : ∀ {ss : Vec S n} → (i : Fin n) → PR hr n ⟨ ss , lookup ss i ⟩
    --   C : ∀ {s m} {ss′ : Vec S m} {ss : Vec S n}
    --     → PR hr n ⟨ ss , s ⟩
    --     → HVec (map (λ s → PR hr m ⟨ ss′ , s ⟩) ss)
    --     → PR hr m ⟨ ss′ , s ⟩
    --   P : ∀ {s₀}{n}{ss : Vec S n}
    --     → (res : S → S)
    --     → (h : (s : S) (a : A) → proj₂ (hr a) ≡ s → PR hr ((r a + r a) + n) ⟨ (map res (proj₁ (hr a)) ++ (proj₁ (hr a))) ++ ss , res s ⟩)
    --     → PR hr (suc n) ⟨ s₀ ∷ ss , res s₀ ⟩

    -- {-# TERMINATING #-}
    -- eval  : ∀ {r : Rank A}{hr : HRank S A r} {n} {s* : Vec S n} {s} → PR hr n ⟨ s* , s ⟩ → HVec (map (Alg hr) s*) → Alg hr s
    -- eval* : ∀ {r : Rank A}{hr : HRank S A r} {n} {s* : Vec S n} {m} {ss : Vec S m} → HVec (map (λ s → PR hr n ⟨ s* , s ⟩) ss) → HVec (map (Alg hr) s*) → HVec (map (Alg hr) ss)

    -- eval (σ a) v* = con a v*
    -- eval{hr = hr}{s* = s*} (π i) v* rewrite sym (lookup-map i (Alg hr) s*) = hlookup v* i
    -- eval (C f g*) v* = eval f (eval* g* v*)
    -- eval{hr = hr} (P {s₀ = s₀}{ss = ss} res h) (con a x* ∷ᴴ v*)
    --   with x* ++ᴴ v*
    -- ... | arg₂ rewrite ++-map (Alg hr) (proj₁ (hr a)) ss
    --   with mapᴴ {rss = (map (Alg hr ∘ res) (proj₁ (hr a)))} (λ{i} → λ x → asType (eval (P {s₀ = lookup (proj₁ (hr a)) i} res h) (asType x (lookup-map i (Alg hr) (proj₁ (hr a))) ∷ᴴ v*)) (sym (lookup-map i (Alg hr ∘ res) (proj₁ (hr a))))) x*
    -- ... | arg₁ rewrite sym (∘-map (Alg hr) res (proj₁ (hr a)))
    --   with arg₁ ++ᴴ arg₂
    -- ... | arg₀ rewrite (++-map (Alg hr) (map res (proj₁ (hr a))) (proj₁ (hr a) ++ ss)) = eval (h s₀ a refl) {!arg₀!}
    -- --  eval (h s₀ a refl) ((mapᴴ (λ {s} → λ x → eval (P{s₀ = s} res h) (x ∷ᴴ v*)) x* ++ᴴ x*) ++ᴴ v*)

    -- eval*{ss = []} []ᴴ v* = []ᴴ
    -- eval*{ss = _ ∷ _} (p ∷ᴴ p*) v* = eval p v* ∷ᴴ eval* p* v*



  data Alg  {A}{S}{r : Rank A} (hr : HRank S A r) : S → Set
  data Alg* {A}{S}{r : Rank A} (hr : HRank S A r) : ∀ {n} → Vec S n → Set

  data Alg {A}{S}{r} hr where
    con : (a : A) → Alg* hr (proj₁ (hr a)) → Alg hr (proj₂ (hr a)) 
  data Alg* {A}{S}{r} hr where
    []  : Alg* hr []
    _∷_ : ∀ {s : S}{s* : Vec S n} → Alg hr s → Alg* hr s* → Alg* hr (s ∷ s*)
  

  {-# NO_POSITIVITY_CHECK #-}
  data PR {r} (hr : HRank S A r) : (n : ℕ) → Vec S n × S → Set where
    σ : (a : A) → PR hr (r a) (hr a)
    π : ∀ {s* : Vec S n} → (i : Fin n) → PR hr n ⟨ s* , lookup s* i ⟩
    C : ∀ {s m} {ss′ : Vec S m} {ss : Vec S n}
      → (g  : PR hr n ⟨ ss , s ⟩)
      → (f* : HVec (map (λ s → PR hr m ⟨ ss′ , s ⟩) ss))
      → PR hr m ⟨ ss′ , s ⟩
    P : ∀ {s₀}{n}{ss : Vec S n}
      → (res : S → S)
      → (h : (s : S) (a : A) → proj₂ (hr a) ≡ s → PR hr ((r a + r a) + n) ⟨ (map res (proj₁ (hr a)) ++ (proj₁ (hr a))) ++ ss , res s ⟩)
      → PR hr (suc n) ⟨ s₀ ∷ ss , res s₀ ⟩

  -- auxiliaries for navigating Alg*

  alookup : ∀ {r : Rank A}{hr : HRank S A r} {n} {s* : Vec S n} → Alg* hr {n} s* → (i : Fin n) → Alg hr (lookup s* i)
  alookup (x ∷ _) zero = x
  alookup (_ ∷ v*) (suc i) = alookup v* i

  _++ᴬ_ : ∀ {r} {hr : HRank S A r} {ss₁ : Vec S m} {ss₂ : Vec S n} → Alg* hr ss₁ → Alg* hr ss₂ → Alg* hr (ss₁ ++ ss₂)
  [] ++ᴬ w* = w*
  (x ∷ v*) ++ᴬ w* = x ∷ (v* ++ᴬ w*)

  mapᴬ : ∀ {n}{r} {hr : HRank S A r} {ss : Vec S n} {res : S → S} → ((i : Fin n) → Alg hr (lookup ss i) → Alg hr (lookup (map res ss) i)) → Alg* hr ss → Alg* hr (map res ss)
  mapᴬ f [] = []
  mapᴬ f (x ∷ v*) = (f Fin.zero x) ∷ (mapᴬ (f ∘ Fin.suc) v*)

  {-# TERMINATING #-}
  eval  : ∀ {r : Rank A}{hr : HRank S A r} {n} {s* : Vec S n} {s} → PR hr n ⟨ s* , s ⟩ → Alg* hr s* → Alg hr s
  eval* : ∀ {r : Rank A}{hr : HRank S A r} {n} {s* : Vec S n} {m} {ss : Vec S m} → HVec (map (λ s → PR hr n ⟨ s* , s ⟩) ss) → Alg* hr s* → Alg* hr ss

  eval (σ a) v* = con a v*
  eval (π i) v* = alookup v* i
  eval (C g f*) v* = eval g (eval* f* v*)
  eval{hr = hr} (P{s₀ = s₀} res h) (con a x* ∷ v*) = eval (h s₀ a refl) ((mapᴬ (λ i x → subst (Alg hr) (sym (lookup-map i res (proj₁ (hr a)))) (eval (P res h) (x ∷ v*))) x* ++ᴬ x*) ++ᴬ v*)

  eval* {ss = []} []ᴴ v* = []
  eval* {ss = s ∷ ss} (f ∷ᴴ f*) v* = eval f v* ∷ eval* f* v*


-- results

import NatsToWords

import WordsToTrees 


module TreesToHetTrees where

  -- pr on heterogeneous trees simulates pr on trees
  make-sig : ∀ n → Vec ⊤ n × ⊤
  make-sig n = ⟨ repeat n tt , tt ⟩

  make-r : (r : Trees.Rank A) → HTrees2.HRank ⊤ A r
  make-r r = λ a → make-sig (r a)

  ⟦_⟧ : ∀ {r : Trees.Rank A}{n}
    → Trees.PRR r n
    → HTrees2.PR (make-r r) n (make-sig n)
  ⟦_⟧* : ∀ {r : Trees.Rank A}{m}{n}
    → Vec (Trees.PRR r n) m
    → HTrees2.HVec {m} (repeat m (HTrees2.PR (make-r r) n (make-sig n)))

  ⟦ Trees.σ a ⟧ = HTrees2.σ a
  ⟦ Trees.π i ⟧ = HTrees2.π i
  ⟦_⟧ {r = r}{n} (Trees.C{m = m} f g*) = HTrees2.C ⟦ f ⟧ (subst HTrees2.HVec (map-repeat m tt (λ _ → HTrees2.PR (make-r r) n (make-sig n))) ⟦ g* ⟧*)
  -- (HTrees2.mapᴴ (λ {i} → λ x → subst Function.id (sym (lookup-map i (λ s → HTrees2.PR (make-r r) n ⟨ repeat n tt , s ⟩) (repeat m tt))) ⟦ lookup g* i ⟧) (HTrees2.toHVec g*))
  ⟦_⟧ {r = r}{suc n} (Trees.P h) = HTrees2.P (λ{ tt → tt }) λ{ s a refl → subst (λ ss → HTrees2.PR (make-r r) (r a + r a + n) ⟨ ss , tt ⟩) (eq-repeat a)  ⟦ h a ⟧}
    where
      eq-repeat : ∀ a → repeat (r a + r a + n) tt ≡ (map (λ { tt → tt }) (proj₁ (make-r r a)) ++ proj₁ (make-r r a)) ++ repeat n tt
      eq-repeat a = begin
                      repeat (r a + r a + n) tt
                    ≡⟨ ++-repeat {r a + r a} {n} tt ⟩
                      repeat (r a + r a) tt ++ repeat n tt
                    ≡⟨ cong (_++ repeat n tt) (++-repeat {r a}{r a} tt) ⟩
                      (repeat (r a) tt ++ repeat (r a) tt) ++ repeat n tt
                    ≡⟨ cong (_++ repeat n tt) (cong (_++ repeat (r a) tt) (map-repeat (r a) tt (λ _ → tt))) ⟩
                      (map (λ { tt → tt }) (proj₁ (make-r r a)) ++ proj₁ (make-r r a)) ++ repeat n tt
                    ∎

  ⟦ [] ⟧* = HTrees2.[]ᴴ
  ⟦ p ∷ p* ⟧* = ⟦ p ⟧ HTrees2.∷ᴴ ⟦ p* ⟧*

  ⟦_⟧ⱽ  : ∀ {A} {r : Trees.Rank A} → Trees.Alg r → HTrees2.Alg (make-r r) tt
  ⟦_⟧ⱽ* : ∀ {n} {A} {r : Trees.Rank A} → Vec (Trees.Alg r) n → HTrees2.Alg* (make-r r) (proj₁ (make-sig n))

  ⟦ Trees.con a x* ⟧ⱽ = HTrees2.con a ⟦ x* ⟧ⱽ*
  ⟦ [] ⟧ⱽ* = HTrees2.[]
  ⟦ x ∷ v* ⟧ⱽ* = ⟦ x ⟧ⱽ HTrees2.∷ ⟦ v* ⟧ⱽ*

  lookup-alookup : {r : Trees.Rank A} (i : Fin n) (v* : Vec (Trees.Alg r) n)
    → lookup (map ⟦_⟧ⱽ v*) i ≡ HTrees2.alookup ⟦ v* ⟧ⱽ* i
  lookup-alookup zero (x ∷ v*) = refl
  lookup-alookup (suc i) (x ∷ v*) = lookup-alookup i v*

  subst-trans : ∀ {I : Set} {P : I → Set} {i j k : I}
    (p : i ≡ j) (q : j ≡ k) (x : P i) →
    subst P (trans p q) x ≡ subst P q (subst P p x)
  subst-trans refl refl x = refl

  subst-proof-irrelevant : ∀ {I : Set} {P : I → Set} {i j : I}
    (p q : i ≡ j) (x : P i) → subst P p x ≡ subst P q x
  subst-proof-irrelevant p q x rewrite ≡-irrelevant p q = refl

  subst-sym-from : ∀ {I : Set} {P : I → Set} {i j : I}
    (p : i ≡ j) (x : P i) (y : P j) →
    subst P p x ≡ y → x ≡ subst P (sym p) y
  subst-sym-from refl x y eq = eq

  subst-Alg*-cons : ∀ {A}{r : Trees.Rank A}{m}
    {ss ss′ : Vec ⊤ m} (eq : ss ≡ ss′)
    (x : HTrees2.Alg (make-r r) tt) (xs : HTrees2.Alg* (make-r r) ss) →
    subst (HTrees2.Alg* (make-r r)) (cong (tt ∷_) eq) (x HTrees2.∷ xs)
      ≡ x HTrees2.∷ subst (HTrees2.Alg* (make-r r)) eq xs
  subst-Alg*-cons refl x xs = refl

  subst-Alg*-map-repeat-cons : ∀ {A}{r : Trees.Rank A}{m}
    (res : ⊤ → ⊤) (x : HTrees2.Alg (make-r r) (res tt))
    (xs : HTrees2.Alg* (make-r r) (repeat m (res tt))) →
    subst (HTrees2.Alg* (make-r r)) (map-repeat (suc m) tt res)
      (x HTrees2.∷ xs)
      ≡ x HTrees2.∷
        subst (HTrees2.Alg* (make-r r)) (map-repeat m tt res) xs
  subst-Alg*-map-repeat-cons {m = m} res x xs
    rewrite map-repeat m tt res = refl

  subst-Alg*-++ : ∀ {A}{r : Trees.Rank A}{m n}
    {ss ss′ : Vec ⊤ m} (eq : ss ≡ ss′)
    (xs : HTrees2.Alg* (make-r r) ss)
    {us : Vec ⊤ n} (ys : HTrees2.Alg* (make-r r) us) →
    subst (HTrees2.Alg* (make-r r)) (cong (_++ us) eq) (xs HTrees2.++ᴬ ys)
      ≡ subst (HTrees2.Alg* (make-r r)) eq xs HTrees2.++ᴬ ys
  subst-Alg*-++ refl xs ys = refl

  translate-++ : ∀ {A}{r : Trees.Rank A}{m n}
    (xs : Vec (Trees.Alg r) m) (ys : Vec (Trees.Alg r) n) →
    subst (HTrees2.Alg* (make-r r)) (++-repeat {m} {n} tt)
      ⟦ xs ++ ys ⟧ⱽ*
      ≡ ⟦ xs ⟧ⱽ* HTrees2.++ᴬ ⟦ ys ⟧ⱽ*
  translate-++ [] ys = refl
  translate-++ {r = r} {m = suc m} {n} (x ∷ xs) ys =
    trans
      (subst-Alg*-cons (++-repeat {m} {n} tt) ⟦ x ⟧ⱽ ⟦ xs ++ ys ⟧ⱽ*)
      (cong (⟦ x ⟧ⱽ HTrees2.∷_)
        (translate-++ {r = r} {m} {n} xs ys))

  P-index-eq : ∀ {A}{r : Trees.Rank A}{n} (a : A) →
    repeat (r a + r a + n) tt ≡
      (map (λ { tt → tt }) (proj₁ (make-r r a)) ++ proj₁ (make-r r a)) ++
      repeat n tt
  P-index-eq {r = r} {n} a =
    trans (++-repeat {r a + r a} {n} tt)
      (trans
        (cong (_++ repeat n tt) (++-repeat {r a} {r a} tt))
        (cong (_++ repeat n tt)
          (cong (_++ repeat (r a) tt)
            (map-repeat (r a) tt (λ _ → tt)))))

  translation-P-index-eq : ∀ {A}{r : Trees.Rank A}{n} (a : A) →
    repeat (r a + r a + n) tt ≡
      (map (λ { tt → tt }) (proj₁ (make-r r a)) ++ proj₁ (make-r r a)) ++
      repeat n tt
  translation-P-index-eq {r = r} {n} a =
    begin
      repeat (r a + r a + n) tt
    ≡⟨ ++-repeat {r a + r a} {n} tt ⟩
      repeat (r a + r a) tt ++ repeat n tt
    ≡⟨ cong (_++ repeat n tt) (++-repeat {r a} {r a} tt) ⟩
      (repeat (r a) tt ++ repeat (r a) tt) ++ repeat n tt
    ≡⟨ cong (_++ repeat n tt)
         (cong (_++ repeat (r a) tt)
           (map-repeat (r a) tt (λ _ → tt))) ⟩
      (map (λ { tt → tt }) (proj₁ (make-r r a)) ++
        proj₁ (make-r r a)) ++ repeat n tt
    ∎

  eval-subst-PR : ∀ {A}{r : Trees.Rank A}{n}{s : ⊤}
    {ss ss′ : Vec ⊤ n} (eq : ss ≡ ss′)
    (p : HTrees2.PR (make-r r) n ⟨ ss , s ⟩)
    (v* : HTrees2.Alg* (make-r r) ss′) →
    HTrees2.eval
      (subst (λ us → HTrees2.PR (make-r r) n ⟨ us , s ⟩) eq p) v*
      ≡ HTrees2.eval p
          (subst (HTrees2.Alg* (make-r r)) (sym eq) v*)
  eval-subst-PR refl p v* = refl

  {-# TERMINATING #-}
  sound : ∀ {A}{r : Trees.Rank A} (p : Trees.PRR r n) v*
    → ⟦ Trees.eval {A = A} p v* ⟧ⱽ ≡ HTrees2.eval ⟦ p ⟧ ⟦ v* ⟧ⱽ*
  sound* : ∀ {A}{r : Trees.Rank A} (p* : Vec (Trees.PRR r n) m) v*
    → ⟦ Trees.eval* p* v* ⟧ⱽ* ≡ HTrees2.eval* (subst HTrees2.HVec (map-repeat m tt (λ _ → HTrees2.PR (make-r r) n (make-sig n))) ⟦ p* ⟧*) ⟦ v* ⟧ⱽ*

  translate-map-P : ∀ {A}{r : Trees.Rank A}{n k}
    (h : (a : A) → Trees.PRR r (r a + r a + n))
    (v* : Vec (Trees.Alg r) n) (xs : Vec (Trees.Alg r) k) →
    subst (HTrees2.Alg* (make-r r))
      (map-repeat k tt (λ { tt → tt }))
      ⟦ map (λ x → Trees.eval (Trees.P h) (x ∷ v*)) xs ⟧ⱽ*
      ≡ HTrees2.mapᴬ
          (λ i x → subst (HTrees2.Alg (make-r r))
            (sym (lookup-map i (λ { tt → tt }) (repeat k tt)))
            (HTrees2.eval ⟦ Trees.P h ⟧ (x HTrees2.∷ ⟦ v* ⟧ⱽ*)))
          ⟦ xs ⟧ⱽ*
  translate-map-P h v* [] = refl
  translate-map-P {r = r} h v* (x ∷ xs) =
    trans
      (subst-Alg*-map-repeat-cons
        (λ { tt → tt })
        ⟦ Trees.eval (Trees.P h) (x ∷ v*) ⟧ⱽ
        ⟦ map (λ y → Trees.eval (Trees.P h) (y ∷ v*)) xs ⟧ⱽ*)
      (cong₂ HTrees2._∷_
        (sound (Trees.P h) (x ∷ v*))
        (translate-map-P h v* xs))

  P-args-forward : ∀ {A}{r : Trees.Rank A}{n} (a : A)
    (h : (b : A) → Trees.PRR r (r b + r b + n))
    (xs : Vec (Trees.Alg r) (r a)) (v* : Vec (Trees.Alg r) n) →
    subst (HTrees2.Alg* (make-r r)) (P-index-eq {r = r} {n} a)
      ⟦ (map (λ x → Trees.eval (Trees.P h) (x ∷ v*)) xs ++ xs) ++ v* ⟧ⱽ*
      ≡
      (HTrees2.mapᴬ
        (λ i x → subst (HTrees2.Alg (make-r r))
          (sym (lookup-map i (λ { tt → tt }) (repeat (r a) tt)))
          (HTrees2.eval ⟦ Trees.P h ⟧ (x HTrees2.∷ ⟦ v* ⟧ⱽ*)))
        ⟦ xs ⟧ⱽ* HTrees2.++ᴬ ⟦ xs ⟧ⱽ*) HTrees2.++ᴬ ⟦ v* ⟧ⱽ*
  P-args-forward {r = r} {n} a h xs v* =
    let
      recs = map (λ x → Trees.eval (Trees.P h) (x ∷ v*)) xs
      e₀ = ++-repeat {r a + r a} {n} tt
      e₁ = cong (_++ repeat n tt) (++-repeat {r a} {r a} tt)
      e₂ = cong (_++ repeat n tt)
        (cong (_++ repeat (r a) tt)
          (map-repeat (r a) tt (λ { tt → tt })))
    in
    begin
      subst (HTrees2.Alg* (make-r r)) (P-index-eq {r = r} {n} a)
        ⟦ (recs ++ xs) ++ v* ⟧ⱽ*
    ≡⟨ subst-proof-irrelevant
         {P = HTrees2.Alg* (make-r r)}
         (P-index-eq {r = r} {n} a) (trans e₀ (trans e₁ e₂))
         ⟦ (recs ++ xs) ++ v* ⟧ⱽ* ⟩
      subst (HTrees2.Alg* (make-r r)) (trans e₀ (trans e₁ e₂))
        ⟦ (recs ++ xs) ++ v* ⟧ⱽ*
    ≡⟨ subst-trans e₀ (trans e₁ e₂) ⟦ (recs ++ xs) ++ v* ⟧ⱽ* ⟩
      subst (HTrees2.Alg* (make-r r)) (trans e₁ e₂)
        (subst (HTrees2.Alg* (make-r r)) e₀
          ⟦ (recs ++ xs) ++ v* ⟧ⱽ*)
    ≡⟨ cong (subst (HTrees2.Alg* (make-r r)) (trans e₁ e₂))
         (translate-++ {r = r} {m = r a + r a} {n} (recs ++ xs) v*) ⟩
      subst (HTrees2.Alg* (make-r r)) (trans e₁ e₂)
        (⟦ recs ++ xs ⟧ⱽ* HTrees2.++ᴬ ⟦ v* ⟧ⱽ*)
    ≡⟨ subst-trans e₁ e₂
         (⟦ recs ++ xs ⟧ⱽ* HTrees2.++ᴬ ⟦ v* ⟧ⱽ*) ⟩
      subst (HTrees2.Alg* (make-r r)) e₂
        (subst (HTrees2.Alg* (make-r r)) e₁
          (⟦ recs ++ xs ⟧ⱽ* HTrees2.++ᴬ ⟦ v* ⟧ⱽ*))
    ≡⟨ cong (subst (HTrees2.Alg* (make-r r)) e₂)
         (trans
           (subst-Alg*-++ (++-repeat {r a} {r a} tt)
             ⟦ recs ++ xs ⟧ⱽ* ⟦ v* ⟧ⱽ*)
           (cong (λ zs → zs HTrees2.++ᴬ ⟦ v* ⟧ⱽ*)
             (translate-++ {r = r} {m = r a} {n = r a} recs xs))) ⟩
      subst (HTrees2.Alg* (make-r r)) e₂
        ((⟦ recs ⟧ⱽ* HTrees2.++ᴬ ⟦ xs ⟧ⱽ*) HTrees2.++ᴬ ⟦ v* ⟧ⱽ*)
    ≡⟨ trans
         (subst-Alg*-++
           (cong (_++ repeat (r a) tt)
             (map-repeat (r a) tt (λ { tt → tt })))
           (⟦ recs ⟧ⱽ* HTrees2.++ᴬ ⟦ xs ⟧ⱽ*) ⟦ v* ⟧ⱽ*)
         (cong (λ zs → zs HTrees2.++ᴬ ⟦ v* ⟧ⱽ*)
           (trans
             (subst-Alg*-++
               (map-repeat (r a) tt (λ { tt → tt }))
               ⟦ recs ⟧ⱽ* ⟦ xs ⟧ⱽ*)
             (cong (λ zs → zs HTrees2.++ᴬ ⟦ xs ⟧ⱽ*)
               (translate-map-P {r = r} {n} {k = r a} h v* xs)))) ⟩
      (HTrees2.mapᴬ
        (λ i x → subst (HTrees2.Alg (make-r r))
          (sym (lookup-map i (λ { tt → tt }) (repeat (r a) tt)))
          (HTrees2.eval ⟦ Trees.P h ⟧ (x HTrees2.∷ ⟦ v* ⟧ⱽ*)))
        ⟦ xs ⟧ⱽ* HTrees2.++ᴬ ⟦ xs ⟧ⱽ*) HTrees2.++ᴬ ⟦ v* ⟧ⱽ*
    ∎

  sound-P-hard : ∀ {A}{r : Trees.Rank A}{n}
    (h : (a : A) → Trees.PRR r (r a + r a + n))
    (v* : Vec (Trees.Alg r) (suc n))
    → ⟦ Trees.eval (Trees.P h) v* ⟧ⱽ
      ≡ HTrees2.eval ⟦ Trees.P h ⟧ ⟦ v* ⟧ⱽ*
  sound-P-hard {r = r} {n} h (Trees.con a x* ∷ v*) =
    let
      source = (map (λ x → Trees.eval (Trees.P h) (x ∷ v*)) x* ++ x*) ++ v*
      target =
        (HTrees2.mapᴬ
          (λ i x → subst (HTrees2.Alg (make-r r))
            (sym (lookup-map i (λ { tt → tt }) (repeat (r a) tt)))
            (HTrees2.eval ⟦ Trees.P h ⟧ (x HTrees2.∷ ⟦ v* ⟧ⱽ*)))
          ⟦ x* ⟧ⱽ* HTrees2.++ᴬ ⟦ x* ⟧ⱽ*) HTrees2.++ᴬ ⟦ v* ⟧ⱽ*
      source-to-target = P-args-forward {r = r} {n} a h x* v*
      target-to-source = subst-sym-from
        {P = HTrees2.Alg* (make-r r)} (P-index-eq {r = r} {n} a)
        ⟦ source ⟧ⱽ* target source-to-target
    in
    begin
      ⟦ Trees.eval (h a) source ⟧ⱽ
    ≡⟨ sound (h a) source ⟩
      HTrees2.eval ⟦ h a ⟧ ⟦ source ⟧ⱽ*
    ≡⟨ cong (HTrees2.eval ⟦ h a ⟧) target-to-source ⟩
      HTrees2.eval ⟦ h a ⟧
        (subst (HTrees2.Alg* (make-r r))
          (sym (P-index-eq {r = r} {n} a)) target)
    ≡⟨ sym (eval-subst-PR {r = r} {n = r a + r a + n}
         (P-index-eq {r = r} {n} a) ⟦ h a ⟧ target) ⟩
      HTrees2.eval
        (subst
          (λ us → HTrees2.PR (make-r r) (r a + r a + n) ⟨ us , tt ⟩)
          (P-index-eq {r = r} {n} a) ⟦ h a ⟧) target
    ≡⟨ cong (λ p → HTrees2.eval p target)
         (subst-proof-irrelevant
           {P = λ us → HTrees2.PR (make-r r) (r a + r a + n) ⟨ us , tt ⟩}
           (P-index-eq {r = r} {n} a)
           (translation-P-index-eq {r = r} {n} a) ⟦ h a ⟧) ⟩
      HTrees2.eval
        (subst
          (λ us → HTrees2.PR (make-r r) (r a + r a + n) ⟨ us , tt ⟩)
          (translation-P-index-eq {r = r} {n} a) ⟦ h a ⟧) target
    ≡⟨⟩
      HTrees2.eval ⟦ Trees.P h ⟧ ⟦ Trees.con a x* ∷ v* ⟧ⱽ*
    ∎

  subst-HVec-map-repeat-cons : ∀ {m} (F : ⊤ → Set) (p : F tt)
    (p* : HTrees2.HVec (repeat m (F tt))) →
    subst HTrees2.HVec (map-repeat (suc m) tt F) (p HTrees2.∷ᴴ p*)
      ≡ p HTrees2.∷ᴴ
        subst HTrees2.HVec (map-repeat m tt F) p*
  subst-HVec-map-repeat-cons {m} F p p*
    rewrite map-repeat m tt F = refl

  sound*-cons-hard : ∀ {A}{r : Trees.Rank A}{m}{n}
    (p : Trees.PRR r n) (p* : Vec (Trees.PRR r n) m)
    (v* : Vec (Trees.Alg r) n)
    → ⟦ Trees.eval* (p ∷ p*) v* ⟧ⱽ*
      ≡ HTrees2.eval*
          (subst HTrees2.HVec
            (map-repeat (suc m) tt
              (λ _ → HTrees2.PR (make-r r) n (make-sig n)))
            ⟦ p ∷ p* ⟧*)
          ⟦ v* ⟧ⱽ*
  sound*-cons-hard {r = r} {m} {n} p p* v*
    = begin
        ⟦ Trees.eval p v* ⟧ⱽ HTrees2.∷ ⟦ Trees.eval* p* v* ⟧ⱽ*
      ≡⟨ cong₂ HTrees2._∷_ (sound p v*) (sound* p* v*) ⟩
        HTrees2.eval ⟦ p ⟧ ⟦ v* ⟧ⱽ* HTrees2.∷
        HTrees2.eval*
          (subst HTrees2.HVec
            (map-repeat m tt
              (λ _ → HTrees2.PR (make-r r) n (make-sig n)))
            ⟦ p* ⟧*) ⟦ v* ⟧ⱽ*
      ≡⟨ sym (cong (λ ps → HTrees2.eval* ps ⟦ v* ⟧ⱽ*)
           (subst-HVec-map-repeat-cons
             (λ _ → HTrees2.PR (make-r r) n (make-sig n)) ⟦ p ⟧ ⟦ p* ⟧*)) ⟩
        HTrees2.eval*
          (subst HTrees2.HVec
            (map-repeat (suc m) tt
              (λ _ → HTrees2.PR (make-r r) n (make-sig n)))
            ⟦ p ∷ p* ⟧*) ⟦ v* ⟧ⱽ*
      ∎

  sound (Trees.σ a) v* = refl
  sound (Trees.π i) v* = begin
                           ⟦ lookup v* i ⟧ⱽ
                         ≡⟨ lookup-map i ⟦_⟧ⱽ v* ⟨
                           lookup (map ⟦_⟧ⱽ v*) i
                         ≡⟨ lookup-alookup i v* ⟩
                           HTrees2.alookup ⟦ v* ⟧ⱽ* i
                         ∎
  sound (Trees.C f g*) v* rewrite sound f (Trees.eval* g* v*) | sound* g* v* = refl
  sound (Trees.P h) v* = sound-P-hard h v*

  sound* [] v* = refl
  sound* (p ∷ p*) v* = sound*-cons-hard p p* v*
\end{code}
