module PrimRecWord where

open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; suc; zero; _*_; _+_)
open import Data.Fin using (Fin)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList)
open import Data.Vec.Properties using (lookup-map)
open import Data.List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_; _++_ to _++ᴸ_; length to lengthᴸ; map to mapᴸ)

variable
  A : Set                       -- alphabet
  m n : ℕ



module Nats where
  data PRN : ℕ → Set where
    Z : PRN n
    S : PRN (suc zero)
    π : (i : Fin n) → PRN n
    C : PRN m → Vec (PRN n) m → PRN n
    P : (g : PRN n) → (h : PRN (suc (suc n))) → PRN (suc n)

  eval  : PRN n → Vec ℕ n → ℕ
  eval* : Vec (PRN n) m → Vec ℕ n → Vec ℕ m

  eval Z        v*           = 0
  eval S        (x ∷ v*)     = suc x
  eval (π i)    v*           = lookup v* i
  eval (C h g*) v*           = eval h (eval* g* v*)
  eval (P g h)  (zero ∷ v*)  = eval g v*
  eval (P g h)  (suc x ∷ v*) = eval h ((eval (P g h) (x ∷ v*)) ∷ (x ∷ v*))

  eval* []       v*          = []
  eval* (p ∷ p*) v*          = eval p v*  ∷ eval* p* v*

module Words where
  data PRW (A : Set) : ℕ → Set where
    Z : PRW A n
    S : (a : A) → PRW A (suc zero)
    π : (i : Fin n) → PRW A n
    C : PRW A m → Vec (PRW A n) m → PRW A n
    P : (g : PRW A n) → (h : A → PRW A (suc (suc n))) → PRW A (suc n)

  eval  : PRW A n → Vec (List A) n → List A
  eval* : Vec (PRW A n) m → Vec (List A) n → Vec (List A) m

  eval Z        v*               = []ᴸ
  eval (S x)    (xs ∷ v*)        = x ∷ᴸ xs
  eval (π i)    v*               = lookup v* i
  eval (C h g*) v*               = eval h (eval* g* v*)
  eval (P g h)  ([]ᴸ ∷ v*)       = eval g v*
  eval (P g h)  ((x ∷ᴸ xs) ∷ v*) = eval (h x) (eval (P g h) (xs ∷ v*) ∷ xs ∷ v*)

  eval* []       v*              = []
  eval* (p ∷ p*) v*              = eval p v* ∷ eval* p* v*

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
  eval (C h g*) v* = eval h (eval* g* v*)
  eval {r = r} (P h) (con a xs ∷ v*) = eval (h a) ((map (λ x → eval (P h) (x ∷ v*)) xs ++ xs) ++ v* )

  eval* [] v* = []
  eval* (x ∷ p*) v* = (eval x v*) ∷ (eval* p* v*)

  --- example
  data Alpha : Set where
    Leaf Branch : Alpha

  rankAlpha : Alpha → ℕ
  rankAlpha Leaf = 0
  rankAlpha Branch = 2

  leaf : Alg rankAlpha
  leaf = con Leaf []

  t1 : Alg rankAlpha
  t1 = con Branch (leaf ∷ (leaf ∷ []))

  -- words as trees
  data Letters : Set where
    ε B C : Letters

  rankLetters : Letters → ℕ
  rankLetters ε = 0
  rankLetters B = 1
  rankLetters C = 1

  epsilon : Alg rankLetters
  epsilon = con ε []

  bc : Alg rankLetters
  bc = con B ((con C (epsilon ∷ [])) ∷ [])

  -- numbers as trees
  data Nums : Set where
    Z S : Nums

  rankNums : Rank Nums
  rankNums Z = 0
  rankNums S = 1

  `zero : Alg rankNums
  `zero = con Z []

  `one  : Alg rankNums
  `one  = con S (`zero ∷ [])

module HetTrees where

  variable
    S : Set                     -- sorts

  module revise-to where
    Rank : Set → Set
    Rank A = A → ℕ

    HRank : Set → (A : Set) → (Rank A) → Set
    HRank S A r = (a : A) → Vec S (r a) × S

  Rank : Set → Set → Set
  Rank S A = A → List S × S     -- List should be Vec...

  data Args (F : S → Set) : List S → Set where
    []ᴬ  : Args F []ᴸ
    _∷ᴬ_ : ∀ {s ss} → F s → Args F ss → Args F (s ∷ᴸ ss)

  alookup : ∀ {ss : Vec S n}{F : S → Set} (a* : Args F (toList ss)) → (i : Fin n) → F (lookup ss i)
  alookup {ss = s ∷ ss} (a ∷ᴬ a*) Fin.zero = a
  alookup {ss = s ∷ ss} (a ∷ᴬ a*) (Fin.suc i) = alookup a* i

  _++ᴬ_ : ∀ {F : S → Set}{ss₁ ss₂ : List S} → Args F ss₁ → Args F ss₂ → Args F (ss₁ ++ᴸ ss₂)
  []ᴬ ++ᴬ ys = ys
  (x ∷ᴬ xs) ++ᴬ ys = x ∷ᴬ (xs ++ᴬ ys)

  mapᴬ : ∀ {F : S → Set}{ss : List S} {res : S → S} → (∀ {s} → F s → F (res s)) → Args F ss → Args F (mapᴸ res ss)
  mapᴬ f []ᴬ = []ᴬ
  mapᴬ f (x ∷ᴬ a*) = f x ∷ᴬ mapᴬ f a*

  data Alg (r : Rank S A) : S → Set where
    con : (a : A) → Args (Alg r) (proj₁ (r a)) → Alg r (proj₂ (r a))

  data PR (r : Rank S A) : List S × S → Set where
    σ : (a : A) → PR r (r a)
    π   : ∀ {ss : Vec S n} → (i : Fin n) → PR r ⟨ toList ss , lookup ss i ⟩
    C   : ∀ {s ss′} {ss} → PR r ⟨ ss , s ⟩ → Args (λ s → PR r ⟨ ss′ , s ⟩) ss → PR r ⟨ ss′ , s ⟩
    P   : ∀ {s₀ ss}
      → (res : S → S)
      → (h : (s : S) (a : A) → proj₂ (r a) ≡ s → PR r ⟨ (mapᴸ res (proj₁ (r a)) ++ᴸ (proj₁ (r a))) ++ᴸ ss , res s ⟩)
      → PR r ⟨ s₀ ∷ᴸ ss , res s₀ ⟩

  {-# TERMINATING #-}
  eval : ∀ {r : Rank S A} {s* s} → PR r ⟨ s* , s ⟩ → Args (Alg r) s* → Alg r s
  eval* : ∀ {r : Rank S A} {s*} {ss} → Args (λ s → PR r ⟨ s* , s ⟩) ss → Args (Alg r) s* → Args (Alg r) ss

  eval (σ a)      a* = con a a*
  eval (π i)      a* = alookup a* i
  eval (C g h)    a* = eval g (eval* h a*)
  eval (P {s₀ = s₀} res h) (con a xs ∷ᴬ a*) =
    eval (h s₀ a refl) ((mapᴬ (λ {s} → λ x → eval (P{s₀ = s} res h) (x ∷ᴬ a*)) xs ++ᴬ xs) ++ᴬ a*)

  eval* []ᴬ       a* = []ᴬ
  eval* (p ∷ᴬ p*) a* = (eval p a*) ∷ᴬ (eval* p* a*)

-- results

module NatsToWords where

  -- pr on words simulates pr on natural numbers

  {-# TERMINATING #-}
  ⟦_⟧ : Nats.PRN n → Words.PRW ⊤ n
  ⟦ Nats.Z ⟧ = Words.Z
  ⟦ Nats.S ⟧ = Words.S tt
  ⟦ Nats.π i ⟧ = Words.π i
  ⟦ Nats.C g h ⟧ = Words.C ⟦ g ⟧ (map ⟦_⟧ h)
  ⟦ Nats.P g h ⟧ = Words.P ⟦ g ⟧ (λ{ tt → ⟦ h ⟧})

  ⟦_⟧ⱽ : ℕ → List ⊤
  ⟦ zero ⟧ⱽ  = []ᴸ
  ⟦ suc n ⟧ⱽ = tt ∷ᴸ ⟦ n ⟧ⱽ

  sound : ∀ {n} p v* → ⟦ Nats.eval {n} p v* ⟧ⱽ ≡ Words.eval ⟦ p ⟧ (map ⟦_⟧ⱽ v*)
  sound* : ∀ {m n} p* v* → map{n = m} ⟦_⟧ⱽ (Nats.eval* {n = n}{m = m} p* v*) ≡ Words.eval* (map ⟦_⟧ p*) (map ⟦_⟧ⱽ v*)

  sound Nats.Z v* = refl
  sound Nats.S (x ∷ []) = refl
  sound (Nats.π i) v* = sym (lookup-map i ⟦_⟧ⱽ v*)
  sound (Nats.C h g*) v* rewrite sound h (Nats.eval* g* v*) | sound* g* v* = refl
  sound (Nats.P g h) (zero ∷ v*) = sound g v*
  sound (Nats.P g h) (suc x ∷ v*) = trans (sound h (Nats.eval (Nats.P g h) (x ∷ v*) ∷ x ∷ v*))
                                          (cong (Words.eval ⟦ h ⟧) 
                                                (cong (_∷ ⟦ x ⟧ⱽ ∷ map ⟦_⟧ⱽ v*)
                                                      (sound (Nats.P g h) (x ∷ v*))))

  sound* [] v* = refl
  sound* (p ∷ p*) v* rewrite sound p v* | sound* p* v* = refl

module WordsToTrees where

  -- pr on trees simulates pr on words
  make-r : ∀ {A : Set} → Trees.Rank (Maybe A)
  make-r nothing = 0
  make-r (just _) = 1
  
  {-# TERMINATING #-}
  ⟦_⟧ : Words.PRW A n → Trees.PRR{Maybe A} (make-r{A}) n
  ⟦ Words.Z ⟧ = Trees.C (Trees.σ nothing) []
  ⟦ Words.S a ⟧ = Trees.σ (just a)
  ⟦ Words.π i ⟧ = Trees.π i
  ⟦ Words.C f g* ⟧ = Trees.C ⟦ f ⟧ (map ⟦_⟧ g*)
  ⟦ Words.P g h ⟧ = Trees.P λ{ nothing → ⟦ g ⟧ ; (just a) → ⟦ h a ⟧}

  ⟦_⟧ⱽ : List A → Trees.Alg (make-r{A})
  ⟦ []ᴸ ⟧ⱽ = Trees.con nothing []
  ⟦ a ∷ᴸ a* ⟧ⱽ = Trees.con (just a) (⟦ a* ⟧ⱽ ∷ [])

  sound : ∀ {n}{A} p v* → ⟦ Words.eval {A = A} {n = n} p v* ⟧ⱽ ≡ Trees.eval ⟦ p ⟧ (map ⟦_⟧ⱽ v*)
  sound* : ∀ {m n A} p* v* → map{n = m} ⟦_⟧ⱽ (Words.eval* {A = A}{n = n}{m = m} p* v*) ≡ Trees.eval* (map ⟦_⟧ p*) (map ⟦_⟧ⱽ v*)

  sound Words.Z v* = refl
  sound (Words.S a) (x ∷ []) = refl
  sound (Words.π i) v* = sym (lookup-map i ⟦_⟧ⱽ v*)
  sound (Words.C f g*) v* rewrite sound f (Words.eval* g* v*) | sound* g* v* = refl
  sound (Words.P g h) ([]ᴸ ∷ v*) = sound g v*
  sound (Words.P g h) ((x ∷ᴸ x₁) ∷ v*) = trans (sound (h x) (Words.eval (Words.P g h) (x₁ ∷ v*) ∷ x₁ ∷ v*))
                                              (cong (Trees.eval ⟦ h x ⟧)
                                                    (cong (_∷ ⟦ x₁ ⟧ⱽ ∷ map ⟦_⟧ⱽ v*)
                                                          (sound (Words.P g h) (x₁ ∷ v*))))

  sound* [] v* = refl
  sound* (p ∷ p*) v* rewrite sound p v* | sound* p* v* = refl

module TreesToHetTrees where

  repeat : ℕ → A → List A
  repeat zero a = []ᴸ
  repeat (suc n) a = a ∷ᴸ repeat n a

  -- pr on heterogeneous trees simulates pr on trees
  make-r : Trees.Rank A → HetTrees.Rank ⊤ A
  make-r r = λ a → ⟨ repeat (r a) tt , tt ⟩

  ⟦_⟧ : ∀ {r : Trees.Rank A}{n} → Trees.PRR r n → HetTrees.PR (make-r r) ⟨ repeat n tt , tt ⟩
  ⟦ Trees.σ a ⟧ = HetTrees.σ a
  ⟦ Trees.π i ⟧ = {!HetTrees.π i!}
  ⟦ Trees.C f g* ⟧ = HetTrees.C ⟦ f ⟧ {!!}
  ⟦ Trees.P h ⟧ = {!!}
