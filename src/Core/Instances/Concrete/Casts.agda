{-# OPTIONS --safe #-}

module Core.Instances.Concrete.Casts where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; cong₂; trans)

open import Core.PRFO
open import Core.Instances.Common
open import Core.Instances.Concrete.Evaluator
open import Core.Instances.Concrete.Supported

castSem : ∀ {T U : TY FO} → T ≡ U → Sem T → Sem U
castSem refl x = x

mapSem : ∀ {T U} → (Sem T → Sem U) → (n : ℕ) →
         Sem (vec T n) → Sem (vec U n)
mapSem f zero tt = tt
mapSem f (suc n) (x , xs) = f x , mapSem f n xs

inj₁-injective : ∀ {A B : Set} {x y : A} →
  _≡_ {A = A ⊎ B} (inj₁ x) (inj₁ y) → x ≡ y
inj₁-injective refl = refl

cast-×-sym : ∀ {A A′ B B′ : TY FO}
  (left : A ≡ A′) (right : B ≡ B′)
  (x : Sem A′) (y : Sem B′) →
  castSem (sym (cong₂ _`×_ left right)) (x , y) ≡
  (castSem (sym left) x , castSem (sym right) y)
cast-×-sym refl refl x y = refl

cast-+-sym₁ : ∀ {A A′ B B′ : TY FO}
  (left : A ≡ A′) (right : B ≡ B′) (x : Sem A′) →
  castSem (sym (cong₂ _`+_ left right)) (inj₁ x) ≡
  inj₁ (castSem (sym left) x)
cast-+-sym₁ refl refl x = refl

cast-+-sym₂ : ∀ {A A′ B B′ : TY FO}
  (left : A ≡ A′) (right : B ≡ B′) (y : Sem B′) →
  castSem (sym (cong₂ _`+_ left right)) (inj₂ y) ≡
  inj₂ (castSem (sym right) y)
cast-+-sym₂ refl refl y = refl

toSubVec : ∀ (n : ℕ) (T : TY FO) →
  Sem (vec T n) → Sem (vec (` zero) n [ T ])
toSubVec n T = castSem (sym (sub-vec n (` zero) (σ₀ T)))

toSubVec-zero : ∀ (T : TY FO) → toSubVec zero T tt ≡ tt
toSubVec-zero T = refl

toSubVec-suc : ∀ (n : ℕ) (T : TY FO)
  (x : Sem T) (xs : Sem (vec T n)) →
  toSubVec (suc n) T (x , xs) ≡ (x , toSubVec n T xs)
toSubVec-suc n T x xs =
  cast-×-sym {A = T} {A′ = T}
    {B = vec (` zero) n [ T ]} {B′ = vec T n}
    refl (sub-vec n (` zero) (σ₀ T)) x xs

toBranches : ∀ {k} (rs : Vec ℕ k) (T : TY FO) →
  Sem (BranchesAt rs T) → Sem (Branches rs [ T ])
toBranches rs T = castSem (sym (branches-sub rs T))

toBranches-inj₁ : ∀ {k} (r : ℕ) (rs : Vec ℕ k) (T : TY FO)
  (xs : Sem (vec T r)) →
  toBranches (r ∷ rs) T (inj₁ xs) ≡
  inj₁ (toSubVec r T xs)
toBranches-inj₁ r rs T xs =
  cast-+-sym₁
    (sub-vec r (` zero) (σ₀ T))
    (branches-sub rs T) xs

toBranches-inj₂ : ∀ {k} (r : ℕ) (rs : Vec ℕ k) (T : TY FO)
  (tail : Sem (BranchesAt rs T)) →
  toBranches (r ∷ rs) T (inj₂ tail) ≡
  inj₂ (toBranches rs T tail)
toBranches-inj₂ r rs T tail =
  cast-+-sym₂
    (sub-vec r (` zero) (σ₀ T))
    (branches-sub rs T) tail

fmap-toSubVec : ∀ {T U} (n : ℕ) (f : Sem T → Sem U)
  (xs : Sem (vec T n)) →
  fmapFlat {G = vec (` zero) n} {T = T} {U = U}
    (flatVec n flat-`) f (toSubVec n T xs) ≡
  toSubVec n U (mapSem f n xs)
fmap-toSubVec zero f tt = refl
fmap-toSubVec {T = T} {U = U} (suc n) f (x , xs)
  rewrite toSubVec-suc n T x xs
        | toSubVec-suc n U (f x) (mapSem f n xs)
        | fmap-toSubVec {T = T} {U = U} n f xs = refl

injectBranch-eval-cast : ∀ {k T} (rs : Vec ℕ k) (i : Fin k)
  (xs : Sem (vec T (lookup rs i))) →
  eval (supported-injectBranch {T = T} rs i) xs ≡
  castSem (sym (branches-sub rs T))
    (eval (supported-injectAt {T = T} rs i) xs)
injectBranch-eval-cast {T = T} rs i xs rewrite branches-sub rs T = refl

fmap-inject-cast : ∀ {k T U} (rs : Vec ℕ k) (i : Fin k)
  (f : Sem T → Sem U) (xs : Sem (vec T (lookup rs i))) →
  fmapFlat {G = Branches rs} {T = T} {U = U} (flatBranches rs) f
    (castSem (sym (branches-sub rs T))
      (eval (supported-injectAt {T = T} rs i) xs)) ≡
  castSem (sym (branches-sub rs U))
    (eval (supported-injectAt {T = U} rs i)
      (mapSem {T = T} {U = U} f (lookup rs i) xs))
fmap-inject-cast {T = T} {U = U} (r ∷ rs) zero f xs
  rewrite toBranches-inj₁ r rs T xs
        | toBranches-inj₁ r rs U (mapSem f r xs)
        | fmap-toSubVec {T = T} {U = U} r f xs = refl
fmap-inject-cast {T = T} {U = U} (r ∷ rs) (suc i) f xs
  rewrite toBranches-inj₂ r rs T
            (eval (supported-injectAt {T = T} rs i) xs)
        | toBranches-inj₂ r rs U
            (eval (supported-injectAt {T = U} rs i) (mapSem f (lookup rs i) xs))
        | fmap-inject-cast {T = T} {U = U} rs i f xs = refl

fmap-injectBranch : ∀ {k T U} (rs : Vec ℕ k) (i : Fin k)
  (f : Sem T → Sem U) (xs : Sem (vec T (lookup rs i))) →
  fmapFlat {G = Branches rs} {T = T} {U = U} (flatBranches rs) f
    (eval (supported-injectBranch {T = T} rs i) xs) ≡
  eval (supported-injectBranch {T = U} rs i)
    (mapSem {T = T} {U = U} f (lookup rs i) xs)
fmap-injectBranch {T = T} {U = U} rs i f xs =
  trans
    (cong (fmapFlat {G = Branches rs} {T = T} {U = U}
      (flatBranches rs) f)
      (injectBranch-eval-cast rs i xs))
    (trans
      (fmap-inject-cast rs i f xs)
      (sym (injectBranch-eval-cast rs i (mapSem f (lookup rs i) xs))))
