\begin{code}[hide]
{-# OPTIONS --rewriting  #-}

module EvalPConstructor where


open import Data.Fin using (Fin; suc; zero; fromℕ; opposite)
open import Data.Nat using (ℕ; suc; zero; _+_; _≟_; _<″?_; _≤ᵇ_; _∸_; _<?_; _<_; _≤‴_; ≤‴-refl; ≤‴-step)
open import Data.Nat.Properties using (≤‴-irrelevant)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map)
open import Data.Vec.Properties using (lookup-++ˡ; map-cong; lookup-++ʳ)
open import Function.Base using (id; _∘_; flip)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; _≗_;cong₂)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Agda.Builtin.Equality.Rewrite
open import FinProperties using (inject+0)
open import VecProperties
open import PR-Nat hiding (para)
open import Relation.Binary
open import Relation.Binary.Core
open import Relation.Nullary
open import Relation.Nullary.Decidable
-- open import Data.Bool hiding (_≟_)

variable
  A : Set
\end{code}

\newcommand{\para}{%
\begin{code}
para : (h : A → ℕ → A) → A → ℕ → A
para h z zero = z
para h z (suc n) = h (para h z n) n
\end{code}
}

\begin{code}[hide]

paraNat' : ∀ {n} → (Vec ℕ n → ℕ) → (Vec ℕ (suc (suc n)) → ℕ) → Vec ℕ ( (suc n)) → ℕ
paraNat' g h (x ∷ args) = para (λ acc n → h (acc ∷ (n ∷ args))) (g args) x


paraNat : ∀ {n} → (Vec ℕ n → ℕ) → (Vec ℕ (suc (suc n)) → ℕ) → Vec ℕ ( (suc n)) → ℕ
paraNat g h (zero ∷ args) = g args
paraNat g h (suc x ∷ args) = h (paraNat g h (x ∷ args) ∷ (x ∷ args))


paraNatPR : ∀ {n : ℕ} (g : PR n) (h : PR (suc (suc n))) (vs : Vec ℕ (suc n) ) → eval (P g h) vs ≡ paraNat (eval g) (eval h) vs
paraNatPR g h (zero ∷ vs) = refl
paraNatPR g h (suc x ∷ vs) rewrite paraNatPR  g h (x ∷ vs)  = refl 

paraNatEq : ∀ {n} → (g : Vec ℕ n → ℕ) → (h : Vec ℕ (suc (suc n)) → ℕ) → (args : Vec ℕ ( (suc n))) → paraNat g h args ≡ paraNat' g h args
paraNatEq g h (zero ∷ args) = refl
paraNatEq g h (suc x ∷ args) rewrite paraNatEq  g h (x ∷ args)  = refl


evalP≡paraNat' : ∀ {n : ℕ} (g : PR n) (h : PR (suc (suc n))) (vs : Vec ℕ (suc n) ) → eval (P g h) vs ≡ paraNat' (eval g) (eval h) vs  -- para (eval g vs) (?) vs 
evalP≡paraNat' g h vs =  (eval (P g h) vs) 
                              ≡⟨ paraNatPR g h vs ⟩ 
                         (paraNat (eval g) (eval h) vs 
                              ≡⟨ paraNatEq (eval g) (eval h) vs ⟩ 
                         (paraNat' (eval g) (eval h) vs) ∎)




-- _<b_ : ℕ → ℕ → Bool
-- n <b m = (suc n)  ≤ᵇ  m


for : ∀ {A : Set} → (acc : A) → (i : ℕ) → (n : ℕ) → (h : A → ℕ → A) → (i ≤‴ n) → A
for acc i .i h ≤‴-refl = acc
for acc i n h (≤‴-step i≤‴n) = for (h acc i) (suc i) n h i≤‴n



n<n+m : (n : ℕ) → (m : ℕ) → n ≤‴ (n + m)
n<n+m n zero = ≤‴-refl
n<n+m n (suc m) = ≤‴-step (n<n+m (suc n) m) 

mk0≤‴n : (n : ℕ) → 0 ≤‴ n
mk0≤‴n n = n<n+m 0 n


for' : ∀ {A : Set} (acc : A) → (n : ℕ) → (h : A → ℕ → A)  → A
for' acc n h = for acc 0 n h (mk0≤‴n n)

≤‴-suc : ∀ {i n} → i ≤‴ n → i ≤‴ suc n
≤‴-suc ≤‴-refl = ≤‴-step ≤‴-refl
≤‴-suc (≤‴-step p) = ≤‴-step (≤‴-suc p)

helper-core : ∀ {A : Set} (acc : A) (i n : ℕ) (h : A → ℕ → A) (p : i ≤‴ n)
  → for acc i (suc n) h (≤‴-suc p) ≡ h (for acc i n h p) n
helper-core acc .n n h ≤‴-refl = refl
helper-core acc i n h (≤‴-step p) = helper-core (h acc i) (suc i) n h p

helper :  ∀ {A : Set} (acc : A) (i : ℕ)→ (n : ℕ) → (h : A → ℕ → A) → (p : i ≤‴ n) → (p' : i ≤‴ (suc n)) →  for acc i (suc n) h p' ≡ h (for acc i n h p ) n
helper acc i n h p p' rewrite ≤‴-irrelevant p' (≤‴-suc p) = helper-core acc i n h p

helper2 :  ∀ {A : Set} (acc : A) (n : ℕ) → (h : A → ℕ → A) →  for' acc (suc n) h ≡ h (for' acc n h) n
helper2 acc n h = helper acc 0 n h (mk0≤‴n n) (mk0≤‴n (suc n))

for'≡para : ∀ {A : Set} (acc : A) → (n : ℕ) → (h : A → ℕ → A)  → para h acc n ≡ for' acc n h
for'≡para acc zero h = refl
for'≡para acc (suc n) h  rewrite helper2 acc n h  = cong₂ h (for'≡para  acc n h) refl




para' : ∀ {A : Set} (h : A → ℕ → A) → A → ℕ → A
para' h acc n = para (λ acc' i → h acc' (n ∸ suc i)) acc n
 
sucN-N≡1 : ∀ (n) → suc n ∸ n ≡ 1
sucN-N≡1 zero = refl
sucN-N≡1 (suc n) = sucN-N≡1 n

N-N≡0 : ∀ (n) →  n ∸ n ≡ 0
N-N≡0 zero = refl
N-N≡0 (suc n) = N-N≡0 n

zero-N≡0 : ∀ (n) → 0 ∸ n ≡ 0
zero-N≡0 zero = refl
zero-N≡0 (suc n) = refl

para'≡para : ∀ {A : Set} (acc : A) → (n : ℕ) → (h : A → ℕ → A)  → para (λ acc' i → h acc' (n ∸  suc i)) acc n ≡ para' h acc n
para'≡para acc n h = refl


\end{code}
