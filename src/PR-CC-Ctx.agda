{-# OPTIONS --rewriting  #-}

module PR-CC-Ctx where


open import Data.Fin using (Fin; zero; suc; _↑ˡ_)
open import Data.Vec.Properties using (lookup-++ʳ; lookup-++ˡ)
open import Data.Empty using (⊥; ⊥-elim)
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
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Utils
open import HVec
open import Agda.Builtin.Equality.Rewrite


import PR-CC-ind as PF


-- infix 6 _→ᴾ_
infix 7 _`×_
infix 8 _`+_


data Ty n :  Set where
  `𝟘   : Ty n
  `𝟙   : Ty n
  _`×_ : Ty n → Ty n → Ty n
  _`+_ : Ty n → Ty n → Ty n
  `    : Fin n → Ty n
  ind  : Ty (suc n) → Ty n
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
mapˢᴿ f `𝟘 = `𝟘
mapˢᴿ f `𝟙 = `𝟙
mapˢᴿ f (tyA `× tyB) = mapˢᴿ f tyA `× mapˢᴿ f tyB
mapˢᴿ f (tyA `+ tyB) = (mapˢᴿ f tyA) `+ (mapˢᴿ f tyB)
mapˢᴿ f (` x) = “ (f x) ”
mapˢᴿ {n'}{m} f (ind ty) = ind (mapˢᴿ (ext {n = n'} f)  ty)
mapˢᴿ eq (tyA ⇒ tyB) = mapˢᴿ eq tyA ⇒ mapˢᴿ eq tyB

map-cong : ∀{n m}{T}{{_ : Mappable T}}{σ τ : T ⊢ n ⇒ m}
  → (∀(x : Fin n) → σ x ≡ τ x)
  → ∀(ty : Ty n)
  → mapˢᴿ σ ty ≡ mapˢᴿ τ ty
map-cong eq `𝟘 = refl
map-cong eq `𝟙 = refl
map-cong {n} {m} {T} eq (tyA `× tyB) = cong₂ _`×_ (map-cong {n} {m} {T} eq tyA) (map-cong {n} {m} {T} eq tyB)
map-cong  {n} {m} {T} eq (tyA `+ tyB) = cong₂ _`+_ (map-cong {n} {m} {T} eq tyA) (map-cong {n} {m} {T} eq tyB)
map-cong eq (` x) = cong “_” (eq x)
map-cong eq (ind ty) = cong ind (map-cong (ext-cong eq) ty)
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
  `abort : ∀ {n : ℕ} {ctx : Ctx n} {T} → Exp ctx `𝟘 → Exp ctx T
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

  con : ∀ {n : ℕ} {ctx : Ctx n} {G} → Exp ctx (sub₀ (ind G) G) → Exp ctx (ind G)
  -- Pr : (h : sub₀ (T `× ind G) G `× U →ᴾ T) → (ind G `× U →ᴾ T)
  Pr : ∀ {n : ℕ} {ctx : Ctx n} {G} {R} → Exp ctx ((sub₀ R G) ⇒ R) → Exp ctx (ind G) → Exp ctx R
⟦_⟧ᵀ : TY → Set


{-# NO_POSITIVITY_CHECK #-}
data Alg (G : Ty 1) : Set where
  con : ⟦ sub₀ (ind G) G ⟧ᵀ → Alg G 

⟦ `𝟘 ⟧ᵀ     = ⊥
⟦ `𝟙 ⟧ᵀ     = ⊤
⟦ T `× U ⟧ᵀ = ⟦ T ⟧ᵀ × ⟦ U ⟧ᵀ
⟦ T `+ U ⟧ᵀ = ⟦ T ⟧ᵀ ⊎ ⟦ U ⟧ᵀ
⟦ ind G ⟧ᵀ  =  Alg G
⟦ tyA ⇒ tyB ⟧ᵀ = ⟦ tyA ⟧ᵀ  →  ⟦ tyB ⟧ᵀ


postulate
  evalPr : ∀ {G R} → (⟦ sub₀ R G ⟧ᵀ → ⟦ R ⟧ᵀ) → Alg G → ⟦ R ⟧ᵀ

eval : ∀ {n : ℕ} {ctx : Ctx n} {ty} → Exp ctx ty →  HVec (λ x → ⟦ x ⟧ᵀ) ctx → ⟦ ty ⟧ᵀ
eval `0 ctx = tt
eval (`abort exp) ctx = ⊥-elim (eval exp ctx)
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
eval (con exp) ctx = con (eval exp ctx)
eval (Pr algebra tree) ctx = evalPr (eval algebra ctx) (eval tree ctx)


embedd-Ty : ∀ {n} → PF.Ty n → Ty n
embedd-Ty PF.`𝟘 = `𝟘
embedd-Ty PF.`𝟙 = `𝟙
embedd-Ty (tyA PF.`× tyB) = embedd-Ty tyA `× embedd-Ty tyB
embedd-Ty (tyA PF.`+ tyB) = embedd-Ty tyA `+ embedd-Ty tyB
embedd-Ty (PF.` x) = ` x
embedd-Ty (PF.ind ty) = ind (embedd-Ty ty) --  ind (embedd-Ty ty)

{-# REWRITE   lookup-++ˡ #-}


weaken : ∀ {n m : ℕ} {ctx : Ctx n} {tyA } (ctx' : Ctx m)  →  Exp ctx tyA → Exp (ctx ++ ctx') tyA
weaken ctx `0 = `0
weaken ctx (`abort exp) = `abort (weaken ctx exp)
weaken ctx (App f x) = App (weaken ctx f) (weaken ctx x)
weaken {n} {m} {ctx} ctx' (Var f)  rewrite lookup-++ˡ ctx ctx' f = Var  {n + m}  (f ↑ˡ m)
weaken ctx (Lam exp) = Lam (weaken ctx exp)
weaken ctx (`# l r) = `# (weaken ctx l) (weaken ctx r)
weaken ctx (π₁ exp) = π₁ (weaken ctx exp)
weaken ctx (π₂ exp) = π₂ (weaken ctx exp)
weaken ctx (ι₁ exp) = ι₁ (weaken ctx exp)
weaken ctx (ι₂ exp) = ι₂ (weaken ctx exp)
weaken ctx (`case c l r) = `case (weaken ctx c) (weaken ctx l) (weaken ctx r) 
weaken ctx (con exp) = con (weaken ctx exp)
weaken ctx (Pr e1 e2) = Pr (weaken ctx e1) (weaken ctx e2)

postulate
  weaken-Eq : ∀ {n m : ℕ} {ctx : Ctx n} {ctx' : Ctx m} {tyA}
    (vals : HVec (λ x → ⟦ x ⟧ᵀ) ctx)
    (vals' : HVec (λ x → ⟦ x ⟧ᵀ) ctx') (exp : Exp ctx tyA)
    → eval (weaken ctx' exp) (vals ++ᴴ vals') ≡ eval exp vals

postulate
  PF→NPF-hard : ∀ {tyA tyB : PF.TY} → tyA PF.→ᴾ tyB → Exp [] (embedd-Ty tyA ⇒ embedd-Ty tyB)

PF→NPF : ∀ {tyA tyB : PF.TY} →  tyA PF.→ᴾ tyB → Exp [] (embedd-Ty tyA ⇒ embedd-Ty tyB )
PF→NPF PF.`⊤ = Lam `0
PF→NPF PF.`⊥ = PF→NPF-hard PF.`⊥
PF→NPF PF.id = Lam (Var zero)
PF→NPF {tyA} {tyB} (PF.C f g) = Lam ( App (weaken [ embedd-Ty tyA ] (PF→NPF f)) (App (weaken [ embedd-Ty tyA ]  (PF→NPF g)) (Var zero))) 
PF→NPF {tyA} {tyB} (PF.`# l r) = Lam (`# 
          (App (weaken [ embedd-Ty tyA ] (PF→NPF l)) (Var zero)) 
          (App (weaken [ embedd-Ty tyA ] (PF→NPF r)) (Var zero))) 
PF→NPF PF.π₁ = Lam (π₁ (Var zero))
PF→NPF PF.π₂ = Lam (π₂ (Var zero))
PF→NPF PF.ι₁ = Lam (ι₁ ((Var zero)))
PF→NPF PF.ι₂ = Lam (ι₂ ((Var zero)))
PF→NPF {(U PF.`+ V)}  (PF.`case f g) = Lam (`case (Var zero) 
          (App (weaken ((embedd-Ty U) ∷ (embedd-Ty U `+ embedd-Ty V ) ∷ [])  (PF→NPF f)) (Var zero)) 
          (App (weaken (embedd-Ty V ∷ embedd-Ty U `+ embedd-Ty V ∷ []) (PF→NPF g)) (Var zero))) 
PF→NPF PF.dist-+-x = PF→NPF-hard PF.dist-+-x
PF→NPF PF.con = PF→NPF-hard PF.con
PF→NPF (PF.Pr exp) = PF→NPF-hard (PF.Pr exp)
PF→NPF (PF.Ct exp) = PF→NPF-hard (PF.Ct exp)

postulate
  ty-eq-ind : ∀ ty → PF.⟦ PF.ind ty ⟧ᵀ ≡ ⟦ embedd-Ty (PF.ind ty) ⟧ᵀ

ty-eq : ∀  (tyA) → PF.⟦ tyA ⟧ᵀ ≡ ⟦ embedd-Ty tyA ⟧ᵀ
ty-eq PF.`𝟘 = refl
ty-eq PF.`𝟙 = refl
ty-eq (tyA PF.`× tyB) = cong₂ _×_ (ty-eq tyA) (ty-eq tyB)
ty-eq (tyA PF.`+ tyB) = cong₂ _⊎_ (ty-eq tyA) (ty-eq tyB)
ty-eq (PF.ind ty) = ty-eq-ind ty


{-# REWRITE ty-eq   #-}

postulate
  PF→NPF-sound-hard : ∀ {tyA tyB : PF.TY} (f : tyA PF.→ᴾ tyB) (arg : PF.⟦ tyA ⟧ᵀ)
    → eval (PF→NPF f) []ᴴ arg ≡ PF.eval f arg

PF→NPF-sound : ∀ {tyA tyB : PF.TY} →  (f : tyA PF.→ᴾ tyB)  → (arg : PF.⟦ tyA ⟧ᵀ  ) → eval  (PF→NPF f) []ᴴ  arg   ≡ PF.eval f arg
PF→NPF-sound PF.`⊤ args = refl
PF→NPF-sound PF.`⊥ ()
PF→NPF-sound PF.id args = refl
PF→NPF-sound (PF.C f g) arg rewrite  
  weaken-Eq []ᴴ (arg ∷ᴴ []ᴴ)  (PF→NPF g) | 
  weaken-Eq []ᴴ (arg ∷ᴴ []ᴴ)  (PF→NPF f) |
  PF→NPF-sound g arg |
  PF→NPF-sound f (PF.eval g arg) = refl 
PF→NPF-sound {tyA} (PF.`# f g) arg rewrite weaken-Eq []ᴴ (arg ∷ᴴ []ᴴ)(PF→NPF f) | weaken-Eq []ᴴ (arg ∷ᴴ []ᴴ)(PF→NPF g) | PF→NPF-sound g arg | PF→NPF-sound f arg = refl 
PF→NPF-sound PF.π₁ args = refl
PF→NPF-sound PF.π₂ args = refl
PF→NPF-sound PF.ι₁ args = refl
PF→NPF-sound PF.ι₂ args = refl
PF→NPF-sound {U PF.`+ V} (PF.`case f g) (inj₁ x) rewrite weaken-Eq {ctx = []} {ctx' = embedd-Ty U ∷ embedd-Ty U `+ embedd-Ty V ∷ [] }  []ᴴ (x ∷ᴴ ((inj₁ x) ∷ᴴ []ᴴ))   (PF→NPF f)  = PF→NPF-sound f x 
PF→NPF-sound {U PF.`+ V} (PF.`case f g) (inj₂ y) rewrite weaken-Eq {ctx = []} {ctx' = embedd-Ty V ∷ embedd-Ty U `+ embedd-Ty V ∷ [] }  []ᴴ (y ∷ᴴ (inj₂ y ∷ᴴ []ᴴ)) (PF→NPF g) = PF→NPF-sound g y
PF→NPF-sound PF.dist-+-x arg = PF→NPF-sound-hard PF.dist-+-x arg
PF→NPF-sound PF.con args = PF→NPF-sound-hard PF.con args
PF→NPF-sound (PF.Pr f) args = PF→NPF-sound-hard (PF.Pr f) args
PF→NPF-sound (PF.Ct f) args = PF→NPF-sound-hard (PF.Ct f) args


-- NPF→PF : ∀ {n : ℕ} {ctx : Ctx n}{tyA tyB : PF.TY} → Exp ctx (embedd-Ty tyA ⇒ embedd-Ty tyB ) → HVec (λ x → ⟦ x ⟧ᵀ) ctx → tyA PF.→ᴾ tyB 
-- NPF→PF   (Var ())   = ?
-- NPF→PF (App f x) ctx = NPF→PF f ctx (NPF→PF x ctx)
-- NPF→PF (Var f) ctx = hlookup ctx f
-- NPF→PF (Lam exp) ctx = λ x → NPF→PF exp (x ∷ᴴ ctx)
-- NPF→PF (`# expL expR) ctx = NPF→PF expL ctx , NPF→PF expR ctx
-- NPF→PF (π₁ exp) ctx = proj₁ (NPF→PF exp ctx)
-- NPF→PF (π₂ exp) ctx = proj₂ (NPF→PF exp ctx)
-- NPF→PF (ι₁ exp) ctx = inj₁ ((NPF→PF exp ctx))
-- NPF→PF (ι₂ exp) ctx = inj₂ ((NPF→PF exp ctx))
-- NPF→PF (`case exp l r) ctx with NPF→PF exp ctx 
-- ... | inj₁ res = NPF→PF l (res ∷ᴴ ctx)
-- ... | inj₂ res = NPF→PF r (res ∷ᴴ ctx)
