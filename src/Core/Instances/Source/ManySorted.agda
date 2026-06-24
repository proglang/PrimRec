{-# OPTIONS --safe #-}

module Core.Instances.Source.ManySorted where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

record Signature (S : Set) : Set₁ where
  constructor signature
  field
    {count} : ℕ
    ranks   : Vec ℕ count
    inputs  : (a : Fin count) → Vec S (lookup ranks a)
    output  : Fin count → S

open Signature public

data PR* {S : Set} (Sig : Signature S) :
  ∀ {n m} → Vec S n × Vec S m → Set

data PR {S : Set} (Sig : Signature S) :
  ∀ {n} → Vec S n × S → Set where
  σ : (a : Fin (count Sig)) → PR Sig (inputs Sig a , output Sig a)
  π : ∀ {n} {ss : Vec S n} (i : Fin n) →
      PR Sig (ss , lookup ss i)
  C : ∀ {n m s} {ss : Vec S n} {us : Vec S m} →
      PR Sig (us , s) → PR* Sig (ss , us) → PR Sig (ss , s)
  P : ∀ {n s₀} {ss : Vec S n} →
      (res : S → S) →
      ((a : Fin (count Sig)) →
        PR Sig ((map res (inputs Sig a) ++ inputs Sig a) ++ ss ,
                res (output Sig a))) →
      PR Sig (s₀ ∷ ss , res s₀)

data PR* {S} Sig where
  []  : ∀ {n} {ss : Vec S n} → PR* Sig (ss , [])
  _∷_ : ∀ {n m} {ss : Vec S n} {s : S} {us : Vec S m} →
        PR Sig (ss , s) → PR* Sig (ss , us) → PR* Sig (ss , s ∷ us)

----------------------------------------------------------------------
-- Intrinsically sorted terms and their concrete evaluator
----------------------------------------------------------------------

data Term {S : Set} (Sig : Signature S) : S → Set where
  con : (a : Fin (count Sig)) →
        ((i : Fin (lookup (ranks Sig) a)) →
          Term Sig (lookup (inputs Sig a) i)) →
        Term Sig (output Sig a)

data Env {S : Set} (Sig : Signature S) :
  ∀ {n} → Vec S n → Set where
  []  : Env Sig []
  _∷_ : ∀ {n s} {ss : Vec S n} →
        Term Sig s → Env Sig ss → Env Sig (s ∷ ss)

lookupEnv : ∀ {S n} {Sig : Signature S} {ss : Vec S n} →
  Env Sig ss → (i : Fin n) → Term Sig (lookup ss i)
lookupEnv (x ∷ xs) zero = x
lookupEnv (x ∷ xs) (suc i) = lookupEnv xs i

appendEnv : ∀ {S m n} {Sig : Signature S}
  {ss : Vec S m} {us : Vec S n} →
  Env Sig ss → Env Sig us → Env Sig (ss ++ us)
appendEnv [] ys = ys
appendEnv (x ∷ xs) ys = x ∷ appendEnv xs ys

tabulateEnv : ∀ {S n} {Sig : Signature S} {ss : Vec S n} →
  ((i : Fin n) → Term Sig (lookup ss i)) → Env Sig ss
tabulateEnv {ss = []} children = []
tabulateEnv {ss = s ∷ ss} children =
  children zero ∷ tabulateEnv (λ i → children (suc i))

tabulateMapEnv : ∀ {S n} {Sig : Signature S} (res : S → S)
  (ss : Vec S n) →
  ((i : Fin n) → Term Sig (res (lookup ss i))) →
  Env Sig (map res ss)
tabulateMapEnv res [] children = []
tabulateMapEnv res (s ∷ ss) children =
  children zero ∷ tabulateMapEnv res ss (λ i → children (suc i))

splitChildren : ∀ {S n} {Sig : Signature S} (res : S → S)
  (ss : Vec S n) →
  ((i : Fin n) → Term Sig (res (lookup ss i)) × Term Sig (lookup ss i)) →
  Env Sig (map res ss) × Env Sig ss
splitChildren res [] children = [] , []
splitChildren res (s ∷ ss) children =
  (proj₁ (children zero) ∷ proj₁ tails) ,
  (proj₂ (children zero) ∷ proj₂ tails)
  where
  tails = splitChildren res ss (λ i → children (suc i))

splitChildren-tabulate : ∀ {S n} {Sig : Signature S} (res : S → S)
  (ss : Vec S n)
  (results : (i : Fin n) → Term Sig (res (lookup ss i)))
  (originals : (i : Fin n) → Term Sig (lookup ss i)) →
  splitChildren res ss (λ i → results i , originals i) ≡
  (tabulateMapEnv res ss results , tabulateEnv originals)
splitChildren-tabulate res [] results originals = refl
splitChildren-tabulate res (s ∷ ss) results originals
  rewrite splitChildren-tabulate res ss
    (λ i → results (suc i)) (λ i → originals (suc i)) = refl

para : ∀ {S s} {Sig : Signature S} (res : S → S) →
  ((a : Fin (count Sig)) →
    ((i : Fin (lookup (ranks Sig) a)) →
      Term Sig (res (lookup (inputs Sig a) i)) ×
      Term Sig (lookup (inputs Sig a) i)) →
    Term Sig (res (output Sig a))) →
  Term Sig s → Term Sig (res s)
para res algebra (con a children) =
  algebra a (λ i → para res algebra (children i) , children i)

eval : ∀ {S n s} {Sig : Signature S} {ss : Vec S n} →
  PR Sig (ss , s) → Env Sig ss → Term Sig s
eval* : ∀ {S n m} {Sig : Signature S}
  {ss : Vec S n} {us : Vec S m} →
  PR* Sig (ss , us) → Env Sig ss → Env Sig us

eval (σ a) values = con a (lookupEnv values)
eval (π i) values = lookupEnv values i
eval (C f fs) values = eval f (eval* fs values)
eval {Sig = Sig} (P res steps) (tree ∷ parameters) =
  para res algebra tree
  where
  algebra : (a : Fin (count Sig)) →
    ((i : Fin (lookup (ranks Sig) a)) →
      Term Sig (res (lookup (inputs Sig a) i)) ×
      Term Sig (lookup (inputs Sig a) i)) →
    Term Sig (res (output Sig a))
  algebra a children with splitChildren res (inputs Sig a) children
  ... | results , originals =
    eval (steps a)
      (appendEnv (appendEnv results originals) parameters)

eval* [] values = []
eval* (p ∷ ps) values = eval p values ∷ eval* ps values

eval-P-con : ∀ {S n} {Sig : Signature S} {ss : Vec S n}
  (res : S → S)
  (steps : (a : Fin (count Sig)) →
    PR Sig ((map res (inputs Sig a) ++ inputs Sig a) ++ ss ,
            res (output Sig a)))
  (a : Fin (count Sig))
  (children : (i : Fin (lookup (ranks Sig) a)) →
    Term Sig (lookup (inputs Sig a) i))
  (parameters : Env Sig ss) →
  eval (P res steps) (con a children ∷ parameters) ≡
  eval (steps a)
    (appendEnv
      (appendEnv
        (tabulateMapEnv res (inputs Sig a)
          (λ i → eval (P res steps) (children i ∷ parameters)))
        (tabulateEnv children))
      parameters)
eval-P-con {Sig = Sig} res steps a children parameters =
  cong
    (λ pair → eval (steps a)
      (appendEnv (appendEnv (proj₁ pair) (proj₂ pair)) parameters))
    (splitChildren-tabulate res (inputs Sig a)
      (λ i → eval (P res steps) (children i ∷ parameters)) children)
