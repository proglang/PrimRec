{-# OPTIONS --safe #-}

module Core.Models.PRHOSet where

open import Data.Fin using (zero)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Level

open import Core.Types
import Core.PRHO as Syn
import Core.Models.PRHO as PRHO

----------------------------------------------------------------------
-- An executable set interpretation for the PR-HO fragment used by the
-- System-T translation.
--
-- Products, coproducts, and exponentials are interpreted by the
-- corresponding Agda type formers.  The natural-number object is
-- represented by IndSem NatF, with constructor nat carrying the actual
-- Agda ℕ.  Other inductive objects are totalized by the placeholder
-- constructor other; the concrete System-T correctness theorem only uses
-- the Nat algebra below.
----------------------------------------------------------------------

NatF : Ty HO 1
NatF = `𝟙 `+ ` zero

Natᴴ : TY HO
Natᴴ = ind NatF

data IndSem : Ty HO 1 → Set where
  nat   : ℕ → IndSem NatF
  other : ∀ {G} → IndSem G

Sem : TY HO → Set
Sem `𝟘 = ⊤
Sem `𝟙 = ⊤
Sem (T `× U) = Sem T × Sem U
Sem (T `+ U) = Sem T ⊎ Sem U
Sem (T `⇒ U) = Sem T → Sem U
Sem (ind G) = IndSem G

default : (T : TY HO) → Sem T
default `𝟘 = tt
default `𝟙 = tt
default (T `× U) = default T , default U
default (T `+ U) = inj₁ (default T)
default (T `⇒ U) = λ _ → default U
default (ind G) = other

fmapSem : ∀ {T U : TY HO} (G : Ty HO 1) →
  (Sem T → Sem U) → Sem (G [ T ]) → Sem (G [ U ])
fmapSem `𝟘 f x = tt
fmapSem `𝟙 f x = x
fmapSem (G `× H) f (x , y) = fmapSem G f x , fmapSem H f y
fmapSem (G `+ H) f (inj₁ x) = inj₁ (fmapSem G f x)
fmapSem (G `+ H) f (inj₂ y) = inj₂ (fmapSem H f y)
fmapSem (A `⇒ G) f g = λ a → fmapSem G f (g a)
fmapSem (` zero) f x = f x
fmapSem (ind G) f x = other

strengthSem : ∀ {T U : TY HO} (G : Ty HO 1) →
  Sem ((G [ T ]) `× U) → Sem (G [ T `× U ])
strengthSem `𝟘 x = tt
strengthSem `𝟙 x = tt
strengthSem (G `× H) ((x , y) , u) =
  strengthSem G (x , u) , strengthSem H (y , u)
strengthSem (G `+ H) (inj₁ x , u) = inj₁ (strengthSem G (x , u))
strengthSem (G `+ H) (inj₂ y , u) = inj₂ (strengthSem H (y , u))
strengthSem (A `⇒ G) (g , u) = λ a → strengthSem G (g a , u)
strengthSem (` zero) (x , u) = x , u
strengthSem (ind G) x = other

conSem : ∀ {G : Ty HO 1} → Sem (G [ ind G ]) → Sem (ind G)
conSem {G = `𝟘} x = other
conSem {G = `𝟙} x = other
conSem {G = G `× H} x = other
conSem {G = `𝟙 `+ ` zero} (inj₁ _) = nat zero
conSem {G = `𝟙 `+ ` zero} (inj₂ (nat n)) = nat (suc n)
conSem {G = `𝟙 `+ ` zero} (inj₂ other) = other
conSem {G = G `+ H} x = other
conSem {G = A `⇒ G} x = other
conSem {G = ` zero} x = other
conSem {G = ind G} x = other

paraNat : ∀ {T U : TY HO} →
  (Sem ((NatF [ T `× Natᴴ ]) `× U) → Sem T) →
  Sem U → ℕ → Sem T
paraNat h u zero = h (inj₁ tt , u)
paraNat h u (suc n) = h (inj₂ (paraNat h u n , nat n) , u)

PSem : ∀ {T U : TY HO} {G : Ty HO 1} →
  (Sem ((G [ T `× ind G ]) `× U) → Sem T) →
  Sem (ind G `× U) → Sem T
PSem {T = T} {G = `𝟘} h x = default T
PSem {T = T} {G = `𝟙} h x = default T
PSem {T = T} {G = G `× H} h x = default T
PSem {G = `𝟙 `+ ` zero} h (nat n , u) = paraNat h u n
PSem {T = T} {G = `𝟙 `+ ` zero} h (other , u) = default T
PSem {T = T} {G = G `+ H} h x = default T
PSem {T = T} {G = A `⇒ G} h x = default T
PSem {T = T} {G = ` zero} h x = default T
PSem {T = T} {G = ind G} h x = default T

structure : PRHO.Structure Level.zero
structure = record
  { _⇒ᴹ_ = λ T U → Sem T → Sem U
  ; idᴹ = λ x → x
  ; Cᴹ = λ f g x → f (g x)
  ; ⊤ᴹ = λ _ → tt
  ; ⊥ᴹ = λ _ → default _
  ; pairᴹ = λ f g x → f x , g x
  ; π₁ᴹ = proj₁
  ; π₂ᴹ = proj₂
  ; ι₁ᴹ = inj₁
  ; ι₂ᴹ = inj₂
  ; caseᴹ = λ f g → λ { (inj₁ x) → f x ; (inj₂ y) → g y }
  ; lamᴹ = λ f x y → f (x , y)
  ; applyᴹ = λ { (f , x) → f x }
  ; fmapᴹ = fmapSem
  ; strengthᴹ = strengthSem
  ; conᴹ = conSem
  ; Pᴹ = PSem
  }

interpret : ∀ {T U : TY HO} → T Syn.→ᴾ U → Sem T → Sem U
interpret = PRHO.interpret structure
