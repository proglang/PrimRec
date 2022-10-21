{-# OPTIONS --rewriting  #-}

module PR-CC-Ctx-ind-alt where


open import Data.Fin using (Fin; zero; suc; inject+)
open import Data.Vec.Properties using (lookup-++ʳ; lookup-++ˡ)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; [] ; _∷_; concat)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Vec using (Vec;[];_∷_;lookup;_++_;map)
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
open import PR-CC-ind-alt using (Ty;PolyTyOp;sub₀;⟦_⟧ₚ;⟦_⟧ᵀ;fold;fmap )
import System-T as ST



import PR-CC-ind-alt as PF
open PF.Ty
open PF.PolyTyOp

open PF.FromNats

TY : Set
TY  = PF.Ty



variable
  T U V : TY
  G : PF.PolyTyOp



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

  fold : ∀ {n : ℕ} {ctx : Ctx n} {G} → Exp ctx (sub₀ (ind G) G) → Exp ctx (ind G)
  -- P : (h : sub₀ (T `× ind G) G `× U →ᴾ T) → (ind G `× U →ᴾ T)
  -- P : ∀ {n : ℕ} {ctx : Ctx n} {G}{P} →  Exp ctx ((sub₀ P G) ⇒ P) → Exp ctx (ind G) → Exp ctx P
  P : ∀ {n : ℕ} {ctx : Ctx n} {G}{P} →  Exp ctx ((sub₀ P G) ⇒ P) → Exp ctx (ind G ⇒  P)




{-# TERMINATING #-}
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
eval (fold exp) ctx = fold (eval exp ctx)
-- eval   (P {G = G} (e1') e2) ctx with eval  e2 ctx
-- ... | fold x = eval e1' ctx 
--                   (fmap  (λ v → {! eval  (Lam (P e1' (Var zero))) ctx !})   G x) 
eval   (P {G = G}{P = p} (e1')) ctx = λ { (fold x) → eval e1' ctx (fmap (λ v → eval (P e1') ctx v) G x)}





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
weaken ctx (fold exp) = fold (weaken ctx exp)
weaken ctx (P e1 ) = P (weaken ctx e1)





weaken-Eq : ∀ {n m : ℕ} {ctx : Ctx n} {ctx' : Ctx m}  {tyA } (vals : HVec (λ x → ⟦ x ⟧ᵀ) ctx ) (vals' : HVec (λ x → ⟦ x ⟧ᵀ) ctx' ) (exp : Exp ctx tyA) → eval (weaken ctx' exp) (vals ++ᴴ vals') ≡ eval exp vals
weaken-Eq = {!   !}

PF→NPF : ∀ {tyA tyB : PF.TY} →  tyA PF.→ᴾ tyB → Exp [] ( tyA ⇒  tyB )
PF→NPF PF.`0 = Lam `0
PF→NPF PF.id = Lam (Var zero)
PF→NPF {tyA} {tyB} (PF.C f g) = Lam ( App (weaken [  tyA ] (PF→NPF f)) (App (weaken [  tyA ]  (PF→NPF g)) (Var zero))) 
PF→NPF {tyA} {tyB} (PF.`# l r) = Lam (`# 
          (App (weaken [  tyA ] (PF→NPF l)) (Var zero)) 
          (App (weaken [  tyA ] (PF→NPF r)) (Var zero))) 
PF→NPF PF.π₁ = Lam (π₁ (Var zero))
PF→NPF PF.π₂ = Lam (π₂ (Var zero))
PF→NPF PF.ι₁ = Lam (ι₁ ((Var zero)))
PF→NPF PF.ι₂ = Lam (ι₂ ((Var zero)))
PF→NPF {(U PF.`+ V)}  (PF.`case f g) = Lam (`case (Var zero) 
          (App (weaken (( U) ∷ ( U `+  V ) ∷ [])  (PF→NPF f)) (Var zero)) 
          (App (weaken ( V ∷  U `+  V ∷ []) (PF→NPF g)) (Var zero))) 
PF→NPF PF.fold = Lam (fold (Var zero))
PF→NPF {(ind G `× U)} (PF.P h) = Lam {!   !} 
PF→NPF (PF.F exp) = {!   !}



PF→NPF-sound : ∀ {tyA tyB : PF.TY} →  (f : tyA PF.→ᴾ tyB)  → (arg : PF.⟦ tyA ⟧ᵀ  ) → eval  (PF→NPF f) []ᴴ  arg   ≡ PF.eval f arg
PF→NPF-sound PF.`0 args = refl
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
PF→NPF-sound {U PF.`+ V} (PF.`case f g) (inj₁ x) rewrite weaken-Eq {ctx = []} {ctx' =  U ∷  U `+  V ∷ [] }  []ᴴ (x ∷ᴴ ((inj₁ x) ∷ᴴ []ᴴ))   (PF→NPF f)  = PF→NPF-sound f x 
PF→NPF-sound {U PF.`+ V} (PF.`case f g) (inj₂ y) rewrite weaken-Eq {ctx = []} {ctx' =  V ∷  U `+  V ∷ [] }  []ᴴ (y ∷ᴴ (inj₂ y ∷ᴴ []ᴴ)) (PF→NPF g) = PF→NPF-sound g y
PF→NPF-sound PF.fold args = refl
PF→NPF-sound (PF.P f) args = {!   !}
PF→NPF-sound (PF.F f) args = {!   !} 




embedd-ST-Ty : ST.Ty → Ty
embedd-ST-Ty ST.TyNat = Nat
embedd-ST-Ty (tyA ST.⇒ tyB) = (embedd-ST-Ty tyA) ⇒ (embedd-ST-Ty tyB)


lookupMap : ∀ {A B : Set}{n}  (vs : Vec A n) (f : Fin n) (g : A → B) → lookup (map g vs) f ≡ g (lookup vs f) 
lookupMap (x ∷ vs) zero g = refl
lookupMap (v ∷ vs) (suc f) g = lookupMap vs f g

{-# REWRITE   lookupMap #-}


ℕ→Nat : ℕ → PR-CC-ind-alt.Fix G-Nat 
ℕ→Nat zero = fold (inj₁ tt)
ℕ→Nat (suc n) = fold (inj₂ (ℕ→Nat n))

Nat→ℕ : PR-CC-ind-alt.Fix G-Nat → ℕ
Nat→ℕ (fold (inj₁ x)) = zero
Nat→ℕ (fold (inj₂ y)) = suc (Nat→ℕ y)

ℕ→Nat∘Nat→ℕ≡id : ∀ (x) → ℕ→Nat (Nat→ℕ x) ≡ x
ℕ→Nat∘Nat→ℕ≡id (fold (inj₁ x)) = refl
ℕ→Nat∘Nat→ℕ≡id (fold (inj₂ y))  = cong fold (cong inj₂ (ℕ→Nat∘Nat→ℕ≡id y))

Nat→ℕ∘ℕ→Nat≡id : ∀ (x) → Nat→ℕ ( ℕ→Nat x) ≡ x
Nat→ℕ∘ℕ→Nat≡id zero = refl
Nat→ℕ∘ℕ→Nat≡id (suc x) = cong suc (Nat→ℕ∘ℕ→Nat≡id x)

ℕ→ExpNat : ∀ {n}{ctx : Ctx n } →  ℕ → Exp ctx Nat
ℕ→ExpNat zero = fold (ι₁ `0)
ℕ→ExpNat (suc n) = fold (ι₂ (ℕ→ExpNat n))



embedd-ST : ∀ {n}  {ctx : ST.Ctx n} {ty} → ST.Exp ctx ty → Exp (map embedd-ST-Ty ctx) (embedd-ST-Ty ty) 
embedd-ST {n} {ctx} (ST.Var f)  = Var f
embedd-ST (ST.Lam exp) = Lam (embedd-ST exp)
embedd-ST ST.CZero = fold (ι₁ `0)
embedd-ST ST.Suc = Lam (fold (ι₂ (Var zero)))
embedd-ST (ST.App f x) = App (embedd-ST f) (embedd-ST x)
embedd-ST {n} {ctx} {ty} (ST.PrecT h acc counter) = 
        let h' = embedd-ST h 
            acc' = embedd-ST acc
            counter' = embedd-ST counter 
            h'' = Lam (`case (Var zero) {!  acc' !} {! embedd-ST h'   !})
            x = (P {n} {map embedd-ST-Ty ctx}  {G-Nat } {embedd-ST-Ty ty} h'') in 
        App x counter'
embedd-ST (ST.Nat n) = ℕ→ExpNat n



embeddTyEval' : ∀ {ty : ST.Ty} →    ⟦ (embedd-ST-Ty ty) ⟧ᵀ → ST.evalTy ty
embeddTyEval : ∀ {ty : ST.Ty} →   ST.evalTy ty → ⟦ (embedd-ST-Ty ty) ⟧ᵀ 


embeddTyEval' {ST.TyNat} v = Nat→ℕ v
embeddTyEval' {(tyA ST.⇒ tyB)} v = λ x → embeddTyEval' {tyB} (v (embeddTyEval  {tyA} x)) 


embeddTyEval {ST.TyNat} v = ℕ→Nat v
embeddTyEval {(tyA ST.⇒ tyB)} v = λ x → embeddTyEval {tyB} (v (embeddTyEval' {tyA} x))

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g



embeddTyEval∘embeddTyEval'≡id : ∀ {ty : ST.Ty } (v : ⟦ (embedd-ST-Ty ty) ⟧ᵀ) → embeddTyEval (embeddTyEval' {ty} v ) ≡ v
embeddTyEval∘embeddTyEval'≡id {ST.TyNat} v = ℕ→Nat∘Nat→ℕ≡id v
embeddTyEval∘embeddTyEval'≡id {tyA ST.⇒ tyB} v = extensionality (λ x → 
    (embeddTyEval (embeddTyEval' (v (embeddTyEval (embeddTyEval' x))))) 
        ≡⟨ cong ((λ x →  (embeddTyEval (embeddTyEval' (v x))))) (embeddTyEval∘embeddTyEval'≡id {tyA} x) ⟩ 
    embeddTyEval (embeddTyEval' (v x)) 
        ≡⟨ embeddTyEval∘embeddTyEval'≡id {tyB} (v x) ⟩ 
    ((v x) ∎ ))

embeddTyEval'∘embeddTyEval≡id : ∀ {ty : ST.Ty} (v : ST.evalTy ty) → embeddTyEval' (embeddTyEval {ty} v ) ≡ v
embeddTyEval'∘embeddTyEval≡id {ST.TyNat} v = Nat→ℕ∘ℕ→Nat≡id v
embeddTyEval'∘embeddTyEval≡id {tyA ST.⇒ tyB} v = extensionality (λ x → 
      embeddTyEval' (embeddTyEval (v (embeddTyEval' (embeddTyEval x)))) 
          ≡⟨ cong (λ x → embeddTyEval' (embeddTyEval (v x)))  (embeddTyEval'∘embeddTyEval≡id {tyA} x)  ⟩ 
      (embeddTyEval' (embeddTyEval (v x)) 
          ≡⟨ embeddTyEval'∘embeddTyEval≡id {tyB} (v x) ⟩ 
      (v x) ∎))

{-# REWRITE   embeddTyEval∘embeddTyEval'≡id #-}

ℕ→Nat≡eval∘ℕ→ExpNat :  ∀ {n}  {ctx : Ctx n} (x : ℕ) (ctx' : HVec (λ x → ⟦ x ⟧ᵀ) ctx) →  ℕ→Nat x ≡ eval (ℕ→ExpNat x) ctx'
ℕ→Nat≡eval∘ℕ→ExpNat zero ctx = refl
ℕ→Nat≡eval∘ℕ→ExpNat (suc x) ctx = cong fold (cong inj₂ (ℕ→Nat≡eval∘ℕ→ExpNat x ctx))


lookupMapᴴ : ∀ {S T : Set} {F : S → Set}{G : T → Set}{n}{ss : Vec S n} {res : S → T} → (i : Fin n) → (f : ∀ {s} → F s → G (res s)) → (hvs : HVec F ss) → f (hlookup  hvs i ) ≡ hlookup (mapᴴ' {S}{T}{F}{G}{n}{ss}{res} f hvs) i
lookupMapᴴ zero f (x ∷ᴴ hvs) = refl
lookupMapᴴ (suc i) f (x ∷ᴴ hvs) = lookupMapᴴ i f hvs



embedd-ST-sound : ∀ {n}  {ctx : ST.Ctx n} {ty} → (ctx' : HVec ST.evalTy ctx) → (sTExp : ST.Exp ctx ty)  → embeddTyEval {ty} ((ST.evalExp sTExp ctx') ) ≡  ( eval (embedd-ST sTExp) (mapᴴ' (embeddTyEval) ctx') ) 
embedd-ST-sound  ( ctx') (ST.Var ( f)) = lookupMapᴴ f embeddTyEval ctx' 
embedd-ST-sound ctx' (ST.Lam exp) = extensionality (λ x → embedd-ST-sound (embeddTyEval' x ∷ᴴ ctx') exp)
embedd-ST-sound ctx' ST.CZero = refl
embedd-ST-sound ctx' ST.Suc = extensionality (λ x → cong fold (cong inj₂ (ℕ→Nat∘Nat→ℕ≡id x) ))
embedd-ST-sound {ty = ty} ctx' (ST.App f x) rewrite sym (embedd-ST-sound ctx' f) |  sym (embedd-ST-sound ctx' x) | embeddTyEval'∘embeddTyEval≡id (ST.evalExp x ctx') = refl 
embedd-ST-sound ctx' (ST.Nat x) = ℕ→Nat≡eval∘ℕ→ExpNat x ((mapᴴ' (embeddTyEval) ctx'))
embedd-ST-sound ctx' (ST.PrecT h acc counter) = {!   !} 


