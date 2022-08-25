module PrimRecWord where

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
open import Function using (_∘_)

variable
  A : Set                       -- alphabet
  S : Set                       -- sorts for many-sorted
  m n o : ℕ

repeat : ∀ {ℓ} {A : Set ℓ} → (n : ℕ) → A → Vec A n
repeat zero a = []
repeat (suc n) a = a ∷ repeat n a

++-repeat : ∀ {m} {n} {ℓ} {A : Set ℓ} (x : A) → repeat (m + n) x ≡ repeat m x ++ repeat n x
++-repeat {zero} x = refl
++-repeat {suc m} x = cong (x ∷_) (++-repeat {m} x)

map-repeat : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → ∀ n (x : A) (f : A → B) → repeat n (f x) ≡ map f (repeat n x)
map-repeat zero x f = refl
map-repeat (suc n) x f rewrite map-repeat n x f = refl

++-map : ∀ {ℓ₁ ℓ₂} {m n}{X : Set ℓ₁}{Y : Set ℓ₂} → (f : X → Y)(v* : Vec X m)(w* : Vec X n) → (map f v* ++ map f w*) ≡ map f (v* ++ w*)
++-map f [] w* = refl
++-map f (v ∷ v*) w* = cong (f v ∷_) (++-map f v* w*)

∘-map : ∀ {ℓ₁ ℓ₂ ℓ₃} {n} {X : Set ℓ₁}{Y : Set ℓ₂}{Z : Set ℓ₃} (f : Y → Z) (g : X → Y) (v* : Vec X n) → map f (map g v*) ≡ map (f ∘ g) v*
∘-map f g [] = refl
∘-map f g (v ∷ v*) = cong ((f ∘ g) v ∷_) (∘-map f g v*)

asType : ∀ {A B : Set} → A → A ≡ B → B
asType a refl = a


module asList where

  data HList (F : S → Set) : List S → Set where
    []ᴴ  : HList F []ᴸ
    _∷ᴴ_ : ∀ {s ss} → F s → HList F ss → HList F (s ∷ᴸ ss)


  hlookup : ∀ {ss : Vec S n}{F : S → Set} (a* : HList F (toList ss)) → (i : Fin n) → F (lookup ss i)
  hlookup {ss = s ∷ ss} (a ∷ᴴ a*) Fin.zero = a
  hlookup {ss = s ∷ ss} (a ∷ᴴ a*) (Fin.suc i) = hlookup a* i

  _++ᴴ_ : ∀ {F : S → Set}{ss₁ ss₂ : List S} → HList F ss₁ → HList F ss₂ → HList F (ss₁ ++ᴸ ss₂)
  []ᴴ ++ᴴ ys = ys
  (x ∷ᴴ xs) ++ᴴ ys = x ∷ᴴ (xs ++ᴴ ys)

  mapᴴ : ∀ {F : S → Set}{ss : List S} {res : S → S} → (∀ {s} → F s → F (res s)) → HList F ss → HList F (mapᴸ res ss)
  mapᴴ f []ᴴ = []ᴴ
  mapᴴ f (x ∷ᴴ a*) = f x ∷ᴴ mapᴴ f a*


----------------------------------------------------------------------
-- primitive recursion on ℕ
----------------------------------------------------------------------

module Nats where
  data PRN : ℕ → Set where
    Z : PRN n
    σ : PRN (suc zero)
    π : (i : Fin n) → PRN n
    C : PRN m → Vec (PRN n) m → PRN n
    P : (g : PRN n) → (h : PRN (suc (suc n))) → PRN (suc n)

  eval  : PRN n → Vec ℕ n → ℕ
  eval* : Vec (PRN n) m → Vec ℕ n → Vec ℕ m

  eval Z        v*           = 0
  eval σ        (x ∷ v*)     = suc x
  eval (π i)    v*           = lookup v* i
  eval (C f g*) v*           = eval f (eval* g* v*)
  eval (P g h)  (zero ∷ v*)  = eval g v*
  eval (P g h)  (suc x ∷ v*) = eval h ((eval (P g h) (x ∷ v*)) ∷ (x ∷ v*))

  eval* []       v*          = []
  eval* (p ∷ p*) v*          = eval p v*  ∷ eval* p* v*

-- vector-valued pr on ℕ
-- PR m n encodes functions ℕᵐ → ℕⁿ

module NatsVec where
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

module Nats-NatsVec where

  open Nats
  open NatsVec

  ⟦_⟧ : Nats.PRN m → NatsVec.PR m 1
  ⟦_⟧* : Vec (PRN m) n → NatsVec.PR m n

  ⟦ Z ⟧ = C PR.Z `0
  ⟦ σ ⟧ = PR.σ
  ⟦ π i ⟧ = π i
  ⟦ C g f* ⟧ = PR.C ⟦ g ⟧ ⟦ f* ⟧*
  ⟦ P g h ⟧ = PR.P ⟦ g ⟧ ⟦ h ⟧

  ⟦ [] ⟧* = `0
  ⟦ f ∷ f* ⟧* = ♯ ⟦ f ⟧ ⟦ f* ⟧*

  sound : (p : Nats.PRN m) (v* : Vec ℕ m) → ∀ {r : Vec ℕ o} → Nats.eval p v* ∷ r ≡ NatsVec.eval ⟦ p ⟧ v* ++ r
  sound* : (f* : Vec (Nats.PRN m) n) (v* : Vec ℕ m) → Nats.eval* f* v* ≡ NatsVec.eval ⟦ f* ⟧* v*

  sound Z v* = refl
  sound σ (x ∷ []) = refl
  sound (π i) v* = refl
  sound (C g f*) v* rewrite sound* f* v* = sound g (NatsVec.eval ⟦ f* ⟧* v*)
  sound (P g h) (zero ∷ v*) = sound g v*
  sound (P g h) (suc x ∷ v*) rewrite sound (P g h) (x ∷ v*) {x ∷ v*} = sound h (NatsVec.eval (P ⟦ g ⟧ ⟦ h ⟧) (x ∷ v*) ++ x ∷ v*) 

  sound* [] v* = refl
  sound* (f ∷ f*) v* rewrite sound* f* v* =  sound f v* {NatsVec.eval ⟦ f* ⟧* v*}

----------------------------------------------------------------------
-- primitive recursion on words over alphabet A
----------------------------------------------------------------------

module Words where
  data PRW (A : Set) : ℕ → Set where
    Z : PRW A n
    σ : (a : A) → PRW A (suc zero)
    π : (i : Fin n) → PRW A n
    C : PRW A m → Vec (PRW A n) m → PRW A n
    P : (g : PRW A n) → (h : A → PRW A (suc (suc n))) → PRW A (suc n)

  eval  : PRW A n → Vec (List A) n → List A
  eval* : Vec (PRW A n) m → Vec (List A) n → Vec (List A) m

  eval Z        v*               = []ᴸ
  eval (σ x)    (xs ∷ v*)        = x ∷ᴸ xs
  eval (π i)    v*               = lookup v* i
  eval (C f g*) v*               = eval f (eval* g* v*)
  eval (P g h)  ([]ᴸ ∷ v*)       = eval g v*
  eval (P g h)  ((x ∷ᴸ xs) ∷ v*) = eval (h x) (eval (P g h) (xs ∷ v*) ∷ xs ∷ v*)

  eval* []       v*              = []
  eval* (p ∷ p*) v*              = eval p v* ∷ eval* p* v*

----------------------------------------------------------------------
-- primitive recursion on trees over ranked alphabet A
----------------------------------------------------------------------

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
    `Z `S : Nums

  rankNums : Rank Nums
  rankNums `Z = 0
  rankNums `S = 1

  `zero : Alg rankNums
  `zero = con `Z []

  `one  : Alg rankNums
  `one  = con `S (`zero ∷ [])

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

module NatsToWords where

  -- pr on words simulates pr on natural numbers

  {-# TERMINATING #-}
  ⟦_⟧ : Nats.PRN n → Words.PRW ⊤ n
  ⟦ Nats.Z ⟧ = Words.Z
  ⟦ Nats.σ ⟧ = Words.σ tt
  ⟦ Nats.π i ⟧ = Words.π i
  ⟦ Nats.C f g* ⟧ = Words.C ⟦ f ⟧ (map ⟦_⟧ g*)
  ⟦ Nats.P g h ⟧ = Words.P ⟦ g ⟧ (λ{ tt → ⟦ h ⟧})

  ⟦_⟧ⱽ : ℕ → List ⊤
  ⟦ zero ⟧ⱽ  = []ᴸ
  ⟦ suc n ⟧ⱽ = tt ∷ᴸ ⟦ n ⟧ⱽ

  sound : ∀ {n} p v* → ⟦ Nats.eval {n} p v* ⟧ⱽ ≡ Words.eval ⟦ p ⟧ (map ⟦_⟧ⱽ v*)
  sound* : ∀ {m n} p* v* → map{n = m} ⟦_⟧ⱽ (Nats.eval* {n = n}{m = m} p* v*) ≡ Words.eval* (map ⟦_⟧ p*) (map ⟦_⟧ⱽ v*)

  sound Nats.Z v* = refl
  sound Nats.σ (x ∷ []) = refl
  sound (Nats.π i) v* = sym (lookup-map i ⟦_⟧ⱽ v*)
  sound (Nats.C f g*) v* rewrite sound f (Nats.eval* g* v*) | sound* g* v* = refl
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
  ⟦ Words.σ a ⟧ = Trees.σ (just a)
  ⟦ Words.π i ⟧ = Trees.π i
  ⟦ Words.C f g* ⟧ = Trees.C ⟦ f ⟧ (map ⟦_⟧ g*)
  ⟦ Words.P g h ⟧ = Trees.P λ{ nothing → ⟦ g ⟧ ; (just a) → ⟦ h a ⟧}

  ⟦_⟧ⱽ : List A → Trees.Alg (make-r{A})
  ⟦ []ᴸ ⟧ⱽ = Trees.con nothing []
  ⟦ a ∷ᴸ a* ⟧ⱽ = Trees.con (just a) (⟦ a* ⟧ⱽ ∷ [])

  sound : ∀ {n}{A} p v* → ⟦ Words.eval {A = A} {n = n} p v* ⟧ⱽ ≡ Trees.eval ⟦ p ⟧ (map ⟦_⟧ⱽ v*)
  sound* : ∀ {m n A} p* v* → map{n = m} ⟦_⟧ⱽ (Words.eval* {A = A}{n = n}{m = m} p* v*) ≡ Trees.eval* (map ⟦_⟧ p*) (map ⟦_⟧ⱽ v*)

  sound Words.Z v* = refl
  sound (Words.σ a) (x ∷ []) = refl
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
  ⟦_⟧ {r = r}{n} (Trees.C{m = m} f g*) = HTrees2.C ⟦ f ⟧ (subst Function.id (cong HTrees2.HVec (map-repeat m tt (λ _ → HTrees2.PR (make-r r) n (make-sig n)))) ⟦ g* ⟧*)
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

  sound : ∀ {A}{r : Trees.Rank A} (p : Trees.PRR r n) v*
    → ⟦ Trees.eval {A = A} p v* ⟧ⱽ ≡ HTrees2.eval ⟦ p ⟧ ⟦ v* ⟧ⱽ*
  sound* : ∀ {A}{r : Trees.Rank A} (p* : Vec (Trees.PRR r n) m) v*
    → ⟦ Trees.eval* p* v* ⟧ⱽ* ≡ HTrees2.eval* (subst HTrees2.HVec (map-repeat m tt (λ s → HTrees2.PR (make-r r) n ⟨ proj₁ (make-sig n) , s ⟩)) ⟦ p* ⟧*) ⟦ v* ⟧ⱽ*

  sound (Trees.σ a) v* = refl
  sound (Trees.π i) v* = begin
                           ⟦ lookup v* i ⟧ⱽ
                         ≡˘⟨ lookup-map i ⟦_⟧ⱽ v* ⟩
                           lookup (map ⟦_⟧ⱽ v*) i
                         ≡⟨ lookup-alookup i v* ⟩
                           HTrees2.alookup ⟦ v* ⟧ⱽ* i
                         ∎
  sound (Trees.C f g*) v* = {!!}
  sound (Trees.P h) v* = {!!}

  sound* [] v* = refl
  sound* (p ∷ p*) v* rewrite sound* p* v* = {!!}
