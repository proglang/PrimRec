\begin{code}[hide]
module PR-Functional where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_; _⊔_)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; toList; head)
open import Function using (const)

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Utils hiding (S; o)

----------------------------------------------------------------------
-- primitive recursive functionals on ℕ
----------------------------------------------------------------------
-- according to
--
-- HANDBOOK OF PROOF THEORY
-- CHAPTER VI
-- Godel’s Functional (“Dialectica”) Interpretation
-- Jeremy Avigad, Solomon Feferman
-- http://math.stanford.edu/~feferman/papers/dialectica.pdf

-- (though they don't define a pointfree version, but rather lambda terms)

data Type : Set where
  o : Type
  _⇒_ : (σ : Type) → (τ : Type) → Type

infixr 20 _⇒_

variable ρ σ τ υ : Type

-- levels

lev : Type → ℕ
lev o = 0
lev (σ ⇒ τ) = suc (lev σ) ⊔ lev τ

-- pure types

\\_// : ℕ → Type
\\ zero // = o
\\ suc n // = \\ n // ⇒ o

pure-type-level : ∀ n → lev (\\ n //) ≡ n
pure-type-level zero = refl
pure-type-level (suc n) = cong suc (pure-type-level n)

\end{code}
\newcommand\PRNatFun{
\begin{code}
data PR : Type → Set where
  Z  : PR o                      -- zero
  +1 : PR (o ⇒ o)                -- successor
  App : PR (σ ⇒ τ) → PR σ → PR τ -- application
  K  : PR (σ ⇒ τ ⇒ σ)            -- constant
  S  : PR ((ρ ⇒ σ ⇒ τ) ⇒ (ρ ⇒ σ) ⇒ ρ ⇒ τ)
  R  : (g : PR τ)                -- primitive recursion
     → (h : PR (o ⇒ τ ⇒ τ))
     → PR (o ⇒ τ)
\end{code}
}
\begin{code}[hide]
  Ct : (g : PR τ)                -- catamorphism over nat, can be simulated with Pr
    → (h : PR (τ ⇒ τ))
    → PR (o ⇒ τ)

T⟦_⟧ : Type → Set
T⟦ o ⟧ = ℕ
T⟦ σ ⇒ τ ⟧ = T⟦ σ ⟧ → T⟦ τ ⟧

para : ∀ {B : Set} → B → (ℕ → B → B) → (ℕ → B)
para g h zero = g
para g h (suc x) = h x (para g h x)

catamorphism : ∀ {B : Set} → B → (B → B) → (ℕ → B)
catamorphism g h zero = g
catamorphism g h (suc i) = h (catamorphism g h i)
\end{code}
\newcommand\PRNatFunEval{
\begin{code}
eval : PR σ → T⟦ σ ⟧
eval Z = 0
eval +1 = suc
eval (App f x) = eval f (eval x)
eval K = const
eval S = λ r s t → r t (s t)
eval (R g h) = para (eval g) (eval h)
eval (Ct g h) = catamorphism (eval g) (eval h)
\end{code}
}
\begin{code}[hide]
import PR-Nat as PRN

-- first-order types of n-ary functions
nary : ℕ → Type
nary zero = o
nary (suc n) = o ⇒ nary n

proj : (i : Fin n) → PR (nary n)
proj {suc zero} zero = App (App S K) (K {τ = o})
proj {suc (suc n)} zero = App (App S (App K K)) (proj zero)
proj (suc i) = App K (proj i)

cnst : ∀ n → PR o → PR (nary n)
cnst zero p = p
cnst (suc n) p = App K (cnst n p)

data BVar : ℕ → Set where
  newest : BVar (suc n)
  older : BVar n → BVar (suc n)

data Open (n : ℕ) : Type → Set where
  var : BVar n → Open n o
  closed : PR σ → Open n σ
  _·_ : Open n (σ ⇒ τ) → Open n σ → Open n τ

infixl 25 _·_

I : PR (σ ⇒ σ)
I {σ} = App
  (App (S {ρ = σ} {σ = o ⇒ σ} {τ = σ})
    (K {σ = σ} {τ = o ⇒ σ}))
  (K {σ = σ} {τ = o})

abstract₁ : Open (suc n) σ → Open n (o ⇒ σ)
abstract₁ (var newest) = closed I
abstract₁ (var (older i)) = closed K · var i
abstract₁ (closed p) = closed (App K p)
abstract₁ (f · x) = (closed S · abstract₁ f) · abstract₁ x

arrows : ℕ → Type → Type
arrows zero σ = σ
arrows (suc n) σ = o ⇒ arrows n σ

arrows-shift : ∀ n σ → arrows n (o ⇒ σ) ≡ (o ⇒ arrows n σ)
arrows-shift zero σ = refl
arrows-shift (suc n) σ = cong (o ⇒_) (arrows-shift n σ)

arrows-nary : ∀ n → arrows n o ≡ nary n
arrows-nary zero = refl
arrows-nary (suc n) = cong (o ⇒_) (arrows-nary n)

erase : Open zero σ → PR σ
erase (var ())
erase (closed p) = p
erase (f · x) = App (erase f) (erase x)

close : Open n σ → PR (arrows n σ)
close {zero} p = erase p
close {suc n} {σ} p = subst PR (arrows-shift n σ) (close (abstract₁ p))

snoc : ∀ {A : Set} {n} → Vec A n → A → Vec A (suc n)
snoc [] x = [ x ]
snoc (y ∷ ys) x = y ∷ snoc ys x

all-vars : ∀ n → Vec (BVar n) n
all-vars zero = []
all-vars (suc n) = snoc (map older (all-vars n)) newest

apply-vars : Open n (nary m) → Vec (BVar n) m → Open n o
apply-vars {m = zero} p [] = p
apply-vars {m = suc m} p (i ∷ is) = apply-vars (p · var i) is

instantiate : PR (nary n) → Open n o
instantiate {n} p = apply-vars (closed p) (all-vars n)

apply-arguments : Open n (nary m) → Vec (Open n o) m → Open n o
apply-arguments {m = zero} p [] = p
apply-arguments {m = suc m} p (x ∷ xs) = apply-arguments (p · x) xs

data OpenF (ρ : Type) (n : ℕ) : Type → Set where
  free : OpenF ρ n ρ
  input : BVar n → OpenF ρ n o
  closedF : PR σ → OpenF ρ n σ
  _·F_ : OpenF ρ n (σ ⇒ τ) → OpenF ρ n σ → OpenF ρ n τ

infixl 25 _·F_

abstract-input : OpenF ρ (suc n) σ → OpenF ρ n (o ⇒ σ)
abstract-input free = closedF K ·F free
abstract-input (input newest) = closedF I
abstract-input (input (older i)) = closedF K ·F input i
abstract-input (closedF p) = closedF (App K p)
abstract-input (f ·F x) = (closedF S ·F abstract-input f) ·F abstract-input x

close-inputs : OpenF ρ n σ → OpenF ρ zero (arrows n σ)
close-inputs {n = zero} p = p
close-inputs {ρ} {n = suc n} {σ} p =
  subst (OpenF ρ zero) (arrows-shift n σ) (close-inputs (abstract-input p))

abstract-free : OpenF ρ zero σ → PR (ρ ⇒ σ)
abstract-free free = I
abstract-free (input ())
abstract-free (closedF p) = App K p
abstract-free (f ·F x) = App (App S (abstract-free f)) (abstract-free x)

apply-inputs : OpenF ρ n (nary m) → Vec (BVar n) m → OpenF ρ n o
apply-inputs {m = zero} p [] = p
apply-inputs {m = suc m} p (i ∷ is) = apply-inputs (p ·F input i) is

apply-argumentsF : OpenF ρ n (nary m) → Vec (OpenF ρ n o) m → OpenF ρ n o
apply-argumentsF {m = zero} p [] = p
apply-argumentsF {m = suc m} p (x ∷ xs) = apply-argumentsF (p ·F x) xs

compile-Ct-step : ∀ {n} → PR (nary (1 + n)) → PR (nary n ⇒ nary n)
compile-Ct-step {n} h =
  abstract-free
    (subst (OpenF (nary n) zero) (arrows-nary n)
      (close-inputs
        (apply-argumentsF (closedF h)
          (apply-inputs free (all-vars n) ∷ map input (all-vars n)))))

data OpenP (ρ υ : Type) (n : ℕ) : Type → Set where
  first : OpenP ρ υ n ρ
  second : OpenP ρ υ n υ
  inputP : BVar n → OpenP ρ υ n o
  closedP : PR σ → OpenP ρ υ n σ
  _·P_ : OpenP ρ υ n (σ ⇒ τ) → OpenP ρ υ n σ → OpenP ρ υ n τ

infixl 25 _·P_

abstract-inputP : OpenP ρ υ (suc n) σ → OpenP ρ υ n (o ⇒ σ)
abstract-inputP first = closedP K ·Pr first
abstract-inputP second = closedP K ·Pr second
abstract-inputP (inputP newest) = closedP I
abstract-inputP (inputP (older i)) = closedP K ·Pr inputP i
abstract-inputP (closedP p) = closedP (App K p)
abstract-inputP (f ·Pr x) = (closedP S ·Pr abstract-inputP f) ·Pr abstract-inputP x

close-inputsP : OpenP ρ υ n σ → OpenP ρ υ zero (arrows n σ)
close-inputsP {n = zero} p = p
close-inputsP {ρ} {υ} {n = suc n} {σ} p =
  subst (OpenP ρ υ zero) (arrows-shift n σ)
    (close-inputsP (abstract-inputP p))

abstract-second : OpenP ρ υ zero σ → OpenF ρ zero (υ ⇒ σ)
abstract-second first = closedF K ·F free
abstract-second second = closedF I
abstract-second (inputP ())
abstract-second (closedP p) = closedF (App K p)
abstract-second (f ·Pr x) =
  (closedF S ·F abstract-second f) ·F abstract-second x

apply-inputsP : OpenP ρ υ n (nary m) → Vec (BVar n) m → OpenP ρ υ n o
apply-inputsP {m = zero} p [] = p
apply-inputsP {m = suc m} p (i ∷ is) = apply-inputsP (p ·Pr inputP i) is

apply-argumentsP : OpenP ρ υ n (nary m) →
  Vec (OpenP ρ υ n o) m → OpenP ρ υ n o
apply-argumentsP {m = zero} p [] = p
apply-argumentsP {m = suc m} p (x ∷ xs) = apply-argumentsP (p ·Pr x) xs

compile-Pr-step : ∀ {n} →
  PR (nary (2 + n)) → PR (o ⇒ nary n ⇒ nary n)
compile-Pr-step {n} h =
  abstract-free
    (abstract-second
      (subst (OpenP o (nary n) zero) (arrows-nary n)
        (close-inputsP
          (apply-argumentsP (closedP h)
            (apply-inputsP second (all-vars n) ∷
              first ∷ map inputP (all-vars n))))))

compile-composition-terms : ∀ {n m} →
  Vec (PR (nary n)) m → PR (nary m) → PR (nary n)
compile-composition-terms {n} g* p =
  subst PR (arrows-nary n)
    (close (apply-arguments (closed p) (map instantiate g*)))

⟦_⟧* : Vec (PRN.PR n) m → PR (nary m) → PR (nary n)
⟦_⟧ : PRN.PR n → PR (nary n)
translate-vector : Vec (PRN.PR n) m → Vec (PR (nary n)) m

⟦ PRN.Z ⟧ = Z
⟦ PRN.σ ⟧ = +1
⟦ PRN.π i ⟧ = proj i
⟦ PRN.C p g* ⟧ =  ⟦ g* ⟧*  ⟦ p ⟧
⟦ PRN.Pr g h ⟧ = R ⟦ g ⟧ (compile-Pr-step ⟦ h ⟧)
⟦ PRN.Ct g h ⟧ = Ct ⟦ g ⟧ (compile-Ct-step ⟦ h ⟧)

translate-vector [] = []
translate-vector (g ∷ g*) = ⟦ g ⟧ ∷ translate-vector g*

⟦_⟧* {n}{zero} [] p = cnst n p
⟦_⟧* {n}{suc m} (g ∷ g*) p =
  compile-composition-terms (translate-vector (g ∷ g*)) p

compile-composition : ∀ {n m} →
  Vec (PRN.PR n) (suc m) → PR (nary (suc m)) → PR (nary n)
compile-composition g* p = compile-composition-terms (translate-vector g*) p
\end{code}
\begin{code}[hide]
_ : eval (proj zero) ≡ λ x → x
_ = refl
_ : eval (proj zero) ≡ λ x → λ y → x
_ = refl
_ : eval (proj (suc zero)) ≡ λ x → λ y → y
_ = refl

_ : eval (proj (suc zero)) ≡ λ x → λ y → λ z → y
_ = refl

_ : eval (proj (suc (suc zero))) ≡ λ x → λ y → λ z → z
_ = refl

_ : eval (proj zero) ≡ λ x → λ y → λ z → x
_ = refl

_ : eval (proj zero) ≡ λ x → λ y → λ z → λ w → x
_ = refl

_ : eval (proj (suc (suc (suc zero)))) ≡ λ x → λ y → λ z → λ w → w
_ = refl

_ : eval (proj (suc (suc zero))) ≡ λ x → λ y → λ z w → z
_ = refl
\end{code}
