{-# OPTIONS --rewriting  #-}

module PR-CC-Ctx where


open import Data.Fin using (Fin; zero; suc; inject+)
open import Data.Vec.Properties using (lookup-++ʳ; lookup-++ˡ)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; [] ; _∷_; map; concat)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Vec using (Vec;[];_∷_;lookup;_++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂) renaming (<_,_> to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; const) renaming (id to identity)
import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)
open import Utils
open import HVec
open import Agda.Builtin.Equality.Rewrite


import PR-CC-ind as PF


-- infix 6 _→ᴾ_
infix 7 _`×_
infix 8 _`+_


data Ty n :  Set where
  `𝟙   : Ty n
  _`×_ : Ty n → Ty n → Ty n
  _`+_ : Ty n → Ty n → Ty n
  `    : Fin n → Ty n
  -- ind  : Ty (suc n) → Ty n
  _⇒_ : Ty n → Ty n → Ty n 

TY = Ty 0



_⊢_⇒_ : (ℕ → Set) → ℕ → ℕ → Set
_⊢_⇒_ Trm n m = Fin n → Trm m


record Mappable (Trm : ℕ → Set) : Set where
  field “_”  : ∀{n} → Trm n → Ty n
  field ext : ∀ {n m} → Trm ⊢ n ⇒ m → Trm ⊢ (suc n) ⇒ (suc m)
  field ext-cong : ∀{n m}{σ τ : Trm ⊢ n ⇒ m} → (∀ (x : Fin n) → σ x ≡ τ x) → (∀(x : Fin (suc n)) → ext {n} σ x ≡ ext {n} τ x)


open Mappable {{...}} public


mapˢᴿ : ∀ {n m}{Trm}{{_ : Mappable Trm}}
  → (Trm ⊢ n ⇒ m)
    -------------------------
  → (Ty n → Ty m)
mapˢᴿ f `𝟙 = `𝟙
mapˢᴿ f (tyA `× tyB) = mapˢᴿ f tyA `× mapˢᴿ f tyB
mapˢᴿ f (tyA `+ tyB) = (mapˢᴿ f tyA) `+ (mapˢᴿ f tyB)
mapˢᴿ f (` x) = “ (f x) ”
-- mapˢᴿ {n'}{m} f (ind ty) = ind (mapˢᴿ (ext {n = n'} f)  ty)
mapˢᴿ eq (tyA ⇒ tyB) = mapˢᴿ eq tyA ⇒ mapˢᴿ eq tyB

map-cong : ∀{n m}{T}{{_ : Mappable T}}{σ τ : T ⊢ n ⇒ m}
  → (∀(x : Fin n) → σ x ≡ τ x)
  → ∀(ty : Ty n)
  → mapˢᴿ σ ty ≡ mapˢᴿ τ ty
map-cong eq `𝟙 = refl
map-cong {n} {m} {T} eq (tyA `× tyB) = cong₂ _`×_ (map-cong {n} {m} {T} eq tyA) (map-cong {n} {m} {T} eq tyB)
map-cong  {n} {m} {T} eq (tyA `+ tyB) = cong₂ _`+_ (map-cong {n} {m} {T} eq tyA) (map-cong {n} {m} {T} eq tyB)
map-cong eq (` x) = cong “_” (eq x)
-- map-cong eq (ind ty) = cong ind (map-cong (ext-cong eq) ty)
map-cong eq (tyA ⇒ tyB) = cong₂ _⇒_ (map-cong eq tyA) (map-cong eq tyB)

Ren : ℕ → ℕ → Set
Ren n m = Fin ⊢ n ⇒ m

extᴿ : ∀ {n m} → (Fin ⊢ n ⇒ m)
    --------------------------------
  →  Fin ⊢ (suc n) ⇒ (suc m)
extᴿ ρ zero      =  zero
extᴿ ρ (suc x)  =  suc (ρ x)

extᴿ-cong : ∀ {n m} {r1 r2 : Ren n m} → (∀ (f : Fin n) → r1 f ≡ r2 f) → (∀ (f : Fin (suc n)) → extᴿ {n} r1 f ≡ extᴿ {n} r2 f )
extᴿ-cong {n} {m} {r1} {r2} eq zero = refl
extᴿ-cong {n} {m} {r1} {r2} eq (suc f) = cong suc (eq f)

instance
  RenameMappable : Mappable Fin
  RenameMappable = record { “_” = ` ; ext = extᴿ ; ext-cong = extᴿ-cong  }


ren : Ren n m → Ty n → Ty m
ren = mapˢᴿ

Sub : ℕ → ℕ → Set
Sub n m = Ty ⊢ n ⇒ m

extˢ : ∀ {n m} → Sub n m → Sub (suc n) (suc m)
extˢ σ zero    = ` zero
extˢ σ (suc x) =  mapˢᴿ  (suc) (σ x) 


extˢ-cong : ∀ {n m} {s1 s2 : Sub n m} → (∀ (f : Fin n) → s1 f ≡ s2 f) → (∀ (f : Fin (suc n)) → extˢ {n} s1 f ≡ extˢ {n} s2 f )
extˢ-cong {n} {m} {s1} {s2} eq zero = refl
extˢ-cong {n} {m} {s1} {s2} eq (suc f) = cong (mapˢᴿ suc) (eq f) -- cong (ren suc) (eq f)

instance
  SubstMappable : Mappable Ty
  SubstMappable = record { “_” = identity ; ext = extˢ ; ext-cong = extˢ-cong  }

sub : Sub n m → Ty n → Ty m
sub = mapˢᴿ 

idₛ : Sub n n
idₛ x = ` x

_,ₛ_ : Sub m n → Ty n → Sub (suc m) n
(σ ,ₛ t) zero    = t
(σ ,ₛ t) (suc x) = σ x

σ₀ : Ty n → Sub (suc n) n
σ₀ T = idₛ ,ₛ T

sub₀ : Ty 0 → Ty 1 → Ty 0
sub₀ T       = sub (σ₀ T)


variable
  T U V : TY
  G : Ty 1



Ctx : ℕ → Set
Ctx n = Vec TY n

data Exp : ∀ {n : ℕ} → Ctx n → TY → Set where
  `0 :  ∀ {n : ℕ} {ctx : Ctx n} → Exp ctx ( `𝟙)
  App  : ∀ {n : ℕ} {ctx : Ctx n} {tyA tyB} →   Exp ctx (tyA ⇒ tyB) → Exp ctx tyA → Exp ctx tyB
  Var : ∀ {n : ℕ} {ctx : Ctx n}  → (f : Fin n) → Exp ctx (lookup ctx f)
  Lam  : ∀ {n : ℕ} {ctx : Ctx n} { tyA tyB} → Exp (tyA ∷ ctx) tyB → Exp ctx  (tyA ⇒ tyB)


--   --
  `# : ∀ {n : ℕ} {ctx : Ctx n} { tyA tyB} → Exp ctx tyA → Exp ctx tyB → Exp ctx (tyA `× tyB)
  π₁ : ∀ {n : ℕ} {ctx : Ctx n} → Exp ctx (U `× V) → Exp ctx  U
  π₂ : ∀ {n : ℕ} {ctx : Ctx n} → Exp ctx (U `× V) → Exp ctx  V
--   --
  ι₁ :  ∀ {n : ℕ} {ctx : Ctx n} →  Exp ctx U → Exp ctx (U `+ V)
  ι₂ : ∀ {n : ℕ} {ctx : Ctx n} → Exp ctx V → Exp ctx (U `+ V)
  `case : ∀ {n : ℕ} {ctx : Ctx n} {tyA tyB tyC : TY} →  Exp ctx (tyA `+ tyB) → Exp (tyA ∷ ctx) (tyC) → Exp (tyB ∷ ctx) (tyC) → Exp (ctx) (tyC)



⟦_⟧ᵀ : TY → Set

⟦ `𝟙 ⟧ᵀ     = ⊤
⟦ T `× U ⟧ᵀ = ⟦ T ⟧ᵀ × ⟦ U ⟧ᵀ
⟦ T `+ U ⟧ᵀ = ⟦ T ⟧ᵀ ⊎ ⟦ U ⟧ᵀ
-- ⟦ ind G ⟧ᵀ  =  Alg G
⟦ tyA ⇒ tyB ⟧ᵀ = ⟦ tyA ⟧ᵀ  →  ⟦ tyB ⟧ᵀ


eval : ∀ {n : ℕ} {ctx : Ctx n} {ty} → Exp ctx ty →  HVec (λ x → ⟦ x ⟧ᵀ) ctx → ⟦ ty ⟧ᵀ
eval `0 ctx = tt
eval (App f x) ctx = eval f ctx (eval x ctx)
eval (Var f) ctx = hlookup ctx f
eval (Lam exp) ctx = λ x → eval exp (x ∷ᴴ ctx)
eval (`# expL expR) ctx = eval expL ctx , eval expR ctx
eval (π₁ exp) ctx = proj₁ (eval exp ctx)
eval (π₂ exp) ctx = proj₂ (eval exp ctx)
eval (ι₁ exp) ctx = inj₁ ((eval exp ctx))
eval (ι₂ exp) ctx = inj₂ ((eval exp ctx))
eval (`case exp l r) ctx with eval exp ctx 
... | inj₁ res = eval l (res ∷ᴴ ctx)
... | inj₂ res = eval r (res ∷ᴴ ctx)

embedd-Ty : ∀ {n} → PF.Ty n → Ty n
embedd-Ty PF.`𝟙 = `𝟙
embedd-Ty (tyA PF.`× tyB) = embedd-Ty tyA `× embedd-Ty tyB
embedd-Ty (tyA PF.`+ tyB) = embedd-Ty tyA `+ embedd-Ty tyB
embedd-Ty (PF.` x) = ` x
embedd-Ty (PF.ind ty) = {!   !} --  ind (embedd-Ty ty)

{-# REWRITE   lookup-++ˡ #-}


weaken : ∀ {n m : ℕ} {ctx : Ctx n} {tyA } (ctx' : Ctx m)  →  Exp ctx tyA → Exp (ctx ++ ctx') tyA
weaken ctx `0 = `0
weaken ctx (App f x) = App (weaken ctx f) (weaken ctx x)
weaken {n} {m} {ctx} ctx' (Var f)  rewrite lookup-++ˡ ctx ctx' f = Var  {n + m}  ((inject+ m f)) 
weaken ctx (Lam exp) = Lam (weaken ctx exp)
weaken ctx (`# l r) = `# (weaken ctx l) (weaken ctx r)
weaken ctx (π₁ exp) = π₁ (weaken ctx exp)
weaken ctx (π₂ exp) = π₂ (weaken ctx exp)
weaken ctx (ι₁ exp) = ι₁ (weaken ctx exp)
weaken ctx (ι₂ exp) = ι₂ (weaken ctx exp)
weaken ctx (`case c l r) = `case (weaken ctx c) (weaken ctx l) (weaken ctx r) 

weaken-Eq : ∀ {n m : ℕ} {ctx : Ctx n} {ctx' : Ctx m}  {tyA } (vals : HVec (λ x → ⟦ x ⟧ᵀ) ctx ) (vals' : HVec (λ x → ⟦ x ⟧ᵀ) ctx' ) (exp : Exp ctx tyA) → eval (weaken ctx' exp) (vals ++ᴴ vals') ≡ eval exp vals
weaken-Eq = {!   !}

embedd-Exp : ∀ {tyA tyB : PF.TY} →  tyA PF.→ᴾ tyB → Exp [] (embedd-Ty tyA ⇒ embedd-Ty tyB )
embedd-Exp PF.`0 = Lam `0
embedd-Exp PF.id = Lam (Var zero)
embedd-Exp {tyA} {tyB} (PF.C f g) = Lam ( App (weaken [ embedd-Ty tyA ] (embedd-Exp f)) (App (weaken [ embedd-Ty tyA ]  (embedd-Exp g)) (Var zero))) 
embedd-Exp {tyA} {tyB} (PF.`# l r) = Lam (`# 
          (App (weaken [ embedd-Ty tyA ] (embedd-Exp l)) (Var zero)) 
          (App (weaken [ embedd-Ty tyA ] (embedd-Exp r)) (Var zero))) 
embedd-Exp PF.π₁ = Lam (π₁ (Var zero))
embedd-Exp PF.π₂ = Lam (π₂ (Var zero))
embedd-Exp PF.ι₁ = Lam (ι₁ ((Var zero)))
embedd-Exp PF.ι₂ = Lam (ι₂ ((Var zero)))
embedd-Exp {(U PF.`+ V)}  (PF.`case f g) = Lam (`case (Var zero) 
          (App (weaken ((embedd-Ty U) ∷ (embedd-Ty U `+ embedd-Ty V ) ∷ [])  (embedd-Exp f)) (Var zero)) 
          (App (weaken (embedd-Ty V ∷ embedd-Ty U `+ embedd-Ty V ∷ []) (embedd-Exp g)) (Var zero))) 
embedd-Exp PF.fold = {!   !}
embedd-Exp (PF.P exp) = {!   !}
embedd-Exp (PF.F exp) = {!   !}


ty-eq : ∀  (tyA) → PF.⟦ tyA ⟧ᵀ ≡ ⟦ embedd-Ty tyA ⟧ᵀ
ty-eq PF.`𝟙 = refl
ty-eq (tyA PF.`× tyB) = cong₂ _×_ (ty-eq tyA) (ty-eq tyB)
ty-eq (tyA PF.`+ tyB) = cong₂ _⊎_ (ty-eq tyA) (ty-eq tyB)
ty-eq (PF.ind ty) = {! ty-eq ty  !}


{-# REWRITE ty-eq   #-}


sound-embedd : ∀ {tyA tyB : PF.TY} →  (f : tyA PF.→ᴾ tyB)  → (arg : PF.⟦ tyA ⟧ᵀ  ) → eval  (embedd-Exp f) []ᴴ  arg   ≡ PF.eval f arg
sound-embedd PF.`0 args = refl
sound-embedd PF.id args = refl
sound-embedd (PF.C f g) arg rewrite  
  weaken-Eq []ᴴ (arg ∷ᴴ []ᴴ)  (embedd-Exp g) | 
  weaken-Eq []ᴴ (arg ∷ᴴ []ᴴ)  (embedd-Exp f) |
  sound-embedd g arg |
  sound-embedd f (PF.eval g arg) = refl 
sound-embedd {tyA} (PF.`# f g) arg rewrite weaken-Eq []ᴴ (arg ∷ᴴ []ᴴ)(embedd-Exp f) | weaken-Eq []ᴴ (arg ∷ᴴ []ᴴ)(embedd-Exp g) | sound-embedd g arg | sound-embedd f arg = refl 
sound-embedd PF.π₁ args = refl
sound-embedd PF.π₂ args = refl
sound-embedd PF.ι₁ args = refl
sound-embedd PF.ι₂ args = refl
sound-embedd (PF.`case f g) (inj₁ x) = {!   !} 
-- rewrite weaken-Eq []ᴴ (x ∷ᴴ (inj₁ x ∷ᴴ []ᴴ)) (embedd-Exp f) | sound-embedd f x | weaken-Eq []ᴴ (x ∷ᴴ (inj₁ x ∷ᴴ []ᴴ)) (embedd-Exp f)  = {!   !}
sound-embedd (PF.`case f g) (inj₂ y) rewrite weaken-Eq []ᴴ (y ∷ᴴ (inj₁ y ∷ᴴ []ᴴ)) (embedd-Exp g) = {!   !}
sound-embedd PF.fold args = {!   !}
sound-embedd (PF.P f) args = {!   !}
sound-embedd (PF.F f) args = {!   !} 


