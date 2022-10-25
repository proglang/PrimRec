{-# OPTIONS --rewriting  #-}

module PR-CC-Ctx-ind-alt where


open import Data.Fin using (Fin; zero; suc; inject+; raise)
open import Data.Vec.Properties using (lookup-++ʳ; lookup-++ˡ)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; [] ; _∷_; concat)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties using (+-suc)
open import Data.Vec using (Vec;[];_∷_;lookup;_++_;map)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; const) renaming (id to identity)
import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst;cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)
open import Utils
open import HVec
open import Agda.Builtin.Equality.Rewrite
open import PR-CC-ind-alt using (Ty;PolyTyOp;sub₀;⟦_⟧ₚ;⟦_⟧ᵀ;fold;fmap;foldF;helper;Fix )
open import EvalPConstructor using (para)
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


-- {-# REWRITE   helper #-}

-- {-# TERMINATING #-}
eval : ∀ {n : ℕ} {ctx : Ctx n} {ty} → Exp ctx ty →  HVec (λ x → ⟦ x ⟧ᵀ) ctx → ⟦ ty ⟧ᵀ
eval `0 ctx = tt
eval (App f x) ctx = eval f ctx (eval x ctx)
eval (Var f) ctx = hlookup ctx f
eval (Lam exp) ctx = λ x → eval exp (x ∷ᴴ ctx)
eval (`# expL expR) ctx = ⟨ eval expL ctx , eval expR ctx ⟩
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
eval   (P {G = G}{P = p} (e1')) ctx = foldF (eval e1' ctx) -- λ { (fold x) → eval e1' ctx (fmap (λ v → eval (P e1') ctx v) G x)}





{-# REWRITE   lookup-++ˡ #-}

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g




weakenGenVar : ∀ (n) (m) (o)→ Fin (n + o) → Fin (n + (m + o))
weakenGenVar zero m o f = raise m f
weakenGenVar (suc n) m o zero = zero
weakenGenVar (suc n) m o (suc f) = suc (weakenGenVar n m o f)

weakenGenVAr-lookup : ∀ {A : Set} {n m o}  (ctxA : Vec A n)(ctxB : Vec A m)(ctxC : Vec A o) (f : Fin (n + o)) → lookup (ctxA ++ ctxB ++ ctxC) (weakenGenVar   n m o f) ≡ lookup (ctxA ++ ctxC) f  
weakenGenVAr-lookup [] ctxB ctxC f = lookup-++ʳ ctxB ctxC f
weakenGenVAr-lookup (x ∷ ctxA) ctxB ctxC zero = refl
weakenGenVAr-lookup (x ∷ ctxA) ctxB ctxC (suc f) = weakenGenVAr-lookup ctxA ctxB ctxC f

{-# REWRITE   weakenGenVAr-lookup lookup-++ʳ #-}

lookup-++ʳᴴ : ∀ {A : Set}{F : A → Set} {n m} {xs : Vec A n} {ys : Vec A m} (hxs : HVec F xs)  (hys : HVec F ys)(f : Fin m )   → hlookup (hxs ++ᴴ hys) (raise n f) ≡ hlookup hys f 
lookup-++ʳᴴ []ᴴ (x ∷ᴴ hys) zero = refl
lookup-++ʳᴴ []ᴴ (x ∷ᴴ hys) (suc f) = refl
lookup-++ʳᴴ (x ∷ᴴ hxs) hys f = lookup-++ʳᴴ hxs hys f


weakenGenVAr-hlookup :  ∀ {A : Set}{F : A → Set}{n m o}  {ctxA : Vec A n} {ctxB : Vec A  m} {ctxC : Vec A o} (valsA : HVec F ctxA ) (valsB : HVec F ctxB )(valsC : HVec F ctxC ) (f : Fin (n + o)) →
  hlookup (valsA ++ᴴ valsB ++ᴴ valsC) (weakenGenVar n m o f) ≡
      hlookup (valsA ++ᴴ valsC) f
weakenGenVAr-hlookup []ᴴ valsB valsC f = lookup-++ʳᴴ valsB valsC f
weakenGenVAr-hlookup (x ∷ᴴ valsA) valsB valsC zero = refl
weakenGenVAr-hlookup (x ∷ᴴ valsA) valsB valsC (suc f) = weakenGenVAr-hlookup valsA valsB valsC f


-- see : https://gitlab.com/goldfirere/stitch/-/blob/hs2020/src/Language/Stitch/Shift.hs
weakenGen : ∀ {n m o}  (ctxA : Ctx n)(ctxB : Ctx m)(ctxC : Ctx o){tyA} → Exp (ctxA ++ ctxC) tyA → Exp (ctxA ++ ctxB ++ ctxC) tyA
weakenGen ctxA ctxB ctxC `0 = `0
weakenGen ctxA ctxB ctxC (App f x) = App (weakenGen ctxA ctxB ctxC f) (weakenGen ctxA ctxB ctxC x)
weakenGen {n} {m}  {o} ctxA ctxB ctxC (Var f) = Var (weakenGenVar  n m o f)
weakenGen ctxA ctxB ctxC (Lam {tyA = tyA } exp) = Lam (weakenGen (tyA ∷ ctxA) ctxB ctxC exp)
weakenGen ctxA ctxB ctxC (`# l r) = `# (weakenGen ctxA ctxB ctxC l) (weakenGen ctxA ctxB ctxC r)
weakenGen ctxA ctxB ctxC (π₁ exp) = π₁ (weakenGen ctxA ctxB ctxC exp)
weakenGen ctxA ctxB ctxC (π₂ exp) = π₂ (weakenGen ctxA ctxB ctxC exp)
weakenGen ctxA ctxB ctxC (ι₁ exp) = ι₁ (weakenGen ctxA ctxB ctxC exp)
weakenGen ctxA ctxB ctxC (ι₂ exp) = ι₂ (weakenGen ctxA ctxB ctxC exp)
weakenGen ctxA ctxB ctxC (`case {tyA = tyA}  {tyB = tyB} c l r) = `case (weakenGen ctxA ctxB ctxC c) (weakenGen (tyA ∷ ctxA) ctxB ctxC l) ((weakenGen (tyB ∷ ctxA) ctxB ctxC r))
weakenGen ctxA ctxB ctxC (fold exp) = fold (weakenGen ctxA ctxB ctxC exp)
weakenGen ctxA ctxB ctxC (P exp) = P (weakenGen ctxA ctxB ctxC exp)



weakenGenEq : ∀ {n m o : ℕ} {ctxA : Ctx n} {ctxB : Ctx m}{ctxC : Ctx o}  {tyA } (valsA : HVec (λ x → ⟦ x ⟧ᵀ) ctxA ) (valsB : HVec (λ x → ⟦ x ⟧ᵀ) ctxB )(valsC : HVec (λ x → ⟦ x ⟧ᵀ) ctxC ) (exp : Exp (ctxA ++ ctxC) tyA) → 
      eval (weakenGen ctxA ctxB ctxC exp) (valsA ++ᴴ valsB ++ᴴ valsC ) ≡ eval exp (valsA ++ᴴ valsC)
weakenGenEq valsA valsB valsC `0 = refl
weakenGenEq valsA valsB valsC (App f x) rewrite weakenGenEq valsA valsB valsC f | weakenGenEq valsA valsB valsC x = refl
weakenGenEq valsA valsB valsC (Var f) = weakenGenVAr-hlookup valsA valsB valsC f
weakenGenEq valsA valsB valsC (Lam {tyA = tyA} exp) = extensionality (λ x → weakenGenEq (x ∷ᴴ valsA) valsB valsC exp)
weakenGenEq valsA valsB valsC (`# l r) = cong₂ ⟨_,_⟩ (weakenGenEq valsA valsB valsC l) (weakenGenEq valsA valsB valsC r)
weakenGenEq valsA valsB valsC (π₁ exp) = cong proj₁ (weakenGenEq valsA valsB valsC exp)
weakenGenEq valsA valsB valsC (π₂ exp) = cong proj₂ (weakenGenEq valsA valsB valsC exp)
weakenGenEq valsA valsB valsC (ι₁ exp) = cong inj₁ (weakenGenEq valsA valsB valsC exp)
weakenGenEq valsA valsB valsC (ι₂ exp) = cong inj₂ (weakenGenEq valsA valsB valsC exp)
weakenGenEq {n}{m}{o} {ctxA}{ctxB} {ctxC} valsA valsB valsC  (`case {tyA = tyA} {tyB = tyB} c l r) 
  rewrite sym (weakenGenEq  valsA valsB valsC c)
  with eval (weakenGen ctxA ctxB ctxC c) (valsA ++ᴴ valsB ++ᴴ valsC )
... | inj₁ x  = weakenGenEq (x ∷ᴴ valsA) valsB valsC l
... | inj₂ y = weakenGenEq (y ∷ᴴ valsA) valsB valsC r
weakenGenEq valsA valsB valsC (fold exp) = cong fold (weakenGenEq valsA valsB valsC exp)
weakenGenEq {n} {m} {o} {ctxA} {ctxB} {ctxC} valsA valsB valsC (P {G = G}{P = ty} exp) rewrite  sym ( weakenGenEq valsA valsB valsC exp)  = refl -- extensionality λ {(fold x) → refl }


weaken : ∀ {n m : ℕ} {ctx : Ctx n} {tyA } (ctx' : Ctx m)  →  Exp ctx tyA → Exp (ctx ++ ctx') tyA
weaken {ctx = ctx} ctx' exp = weakenGen ctx ctx' [] exp
-- weaken ctx `0 = `0
-- weaken ctx (App f x) = App (weaken ctx f) (weaken ctx x)
-- weaken {n} {m} {ctx} ctx' (Var f)  rewrite lookup-++ˡ ctx ctx' f = Var  {n + m}  ((inject+ m f)) 
-- weaken ctx (Lam exp) = Lam (weaken ctx exp)
-- weaken ctx (`# l r) = `# (weaken ctx l) (weaken ctx r)
-- weaken ctx (π₁ exp) = π₁ (weaken ctx exp)
-- weaken ctx (π₂ exp) = π₂ (weaken ctx exp)
-- weaken ctx (ι₁ exp) = ι₁ (weaken ctx exp)
-- weaken ctx (ι₂ exp) = ι₂ (weaken ctx exp)
-- weaken ctx (`case c l r) = `case (weaken ctx c) (weaken ctx l) (weaken ctx r) 
-- weaken ctx (fold exp) = fold (weaken ctx exp)
-- weaken ctx (P e1 ) = P (weaken ctx e1)





weaken-Eq : ∀ {n m : ℕ} {ctx : Ctx n} {ctx' : Ctx m}  {tyA } (vals : HVec (λ x → ⟦ x ⟧ᵀ) ctx ) (vals' : HVec (λ x → ⟦ x ⟧ᵀ) ctx' ) (exp : Exp ctx tyA) → eval (weaken ctx' exp) (vals ++ᴴ vals') ≡ eval exp vals
weaken-Eq vals vals'  = weakenGenEq vals vals' []ᴴ 


weaken' : ∀ {m o} (ctxB : Ctx m){ctxC : Ctx o}{tyA} → Exp ( ctxC) tyA → Exp ( ctxB ++ ctxC) tyA
weaken' ctxB {ctxC} = weakenGen [] ctxB ctxC  


weaken'-Eq : ∀ {m o : ℕ}  {ctxB : Ctx m}{ctxC : Ctx o}  {tyA } (valsB : HVec (λ x → ⟦ x ⟧ᵀ) ctxB )(valsC : HVec (λ x → ⟦ x ⟧ᵀ) ctxC ) (exp : Exp ( ctxC) tyA) → 
      eval (weaken' ctxB {ctxC} exp) (valsB ++ᴴ valsC ) ≡ eval exp (valsC)
weaken'-Eq valsB valsC  = weakenGenEq  []ᴴ  valsB valsC

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
PF→NPF {(ind G `× U)} (PF.P {T} {U} {G} h) = Lam (App (P (Lam (App ((weaken (sub₀ T G ∷ ind G `× U ∷ []) (PF→NPF h))) (`# {! P  !} ((π₂ (Var (suc zero)))))))) (π₁ (Var zero))) 
PF→NPF (PF.F {T} {U} {G} exp) = Lam (App (P (Lam (App (weaken (sub₀ T G ∷ ind G `× U ∷ []) (PF→NPF exp)) (`# (Var zero) (π₂ (Var (suc zero))))))) (π₁ (Var zero))) 


-- λ {(x , u) → foldF (λ gu → eval h (fmap (λ u' → u' , x) G gu , u)) x}
--P : ∀ {n : ℕ} {ctx : Ctx n} {G}{P} →  Exp ctx ((sub₀ P G) ⇒ P) → Exp ctx (ind G ⇒  P)

PF→NPF-sound-Helper : ∀ {T} {U} {G} (f : sub₀ T G `× U PR-CC-ind-alt.→ᴾ T) (x : ⟦ sub₀ T G ⟧ᵀ ) (fst : Fix G) (snd : ⟦ U ⟧ᵀ) → eval (weaken  (sub₀ T G ∷ ind G `× U ∷ []) (PF→NPF f)) (x ∷ᴴ ((⟨ fst , snd ⟩) ∷ᴴ []ᴴ)) (⟨ x , snd ⟩) ≡ PR-CC-ind-alt.eval f (⟨ x , snd ⟩)


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
PF→NPF-sound (PF.P f) arg = {!   !}
PF→NPF-sound (PR-CC-ind-alt.F  {T} {U} {G} f) (⟨ fst , snd ⟩)   = cong₂ foldF {u = fst} {v = fst} (extensionality (λ x →  ( PF→NPF-sound-Helper f x fst snd))) refl

PF→NPF-sound-Helper f x fst snd rewrite weaken-Eq []ᴴ (x ∷ᴴ ((⟨ fst , snd ⟩) ∷ᴴ []ᴴ))  (PF→NPF f) | PF→NPF-sound f (⟨ x , snd ⟩) = refl





embedd-ST-Ty : ST.Ty → Ty
embedd-ST-Ty ST.TyNat = Nat
embedd-ST-Ty (tyA ST.⇒ tyB) = (embedd-ST-Ty tyA) ⇒ (embedd-ST-Ty tyB)


lookupMap : ∀ {A B : Set}{n}  (vs : Vec A n) (f : Fin n) (g : A → B) → lookup (map g vs) f ≡ g (lookup vs f) 
lookupMap (x ∷ vs) zero g = refl
lookupMap (v ∷ vs) (suc f) g = lookupMap vs f g

{-# REWRITE   lookupMap #-}


ℕ→Nat : ℕ → Fix G-Nat 
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

unCurry  : ∀ {n}  {ctx : Ctx n} {tyA tyB tyC : Ty} → Exp ctx (tyA ⇒ (tyB ⇒ tyC))  → Exp ctx ((tyA `× tyB) ⇒ tyC) 
unCurry {n} {ctx} {tyA}      {tyB} f = Lam (App (App (weaken' [ tyA `× tyB ] f) (π₁ (Var zero))) (π₂ (Var zero)))


embedd-ST : ∀ {n}  {ctx : ST.Ctx n} {ty} → ST.Exp ctx ty → Exp (map embedd-ST-Ty ctx) (embedd-ST-Ty ty) 


embedd-ST-P :  ∀ {n}  {ctx : ST.Ctx n} {ty} → (h  : ST.Exp ctx (ty ST.⇒ (ST.TyNat ST.⇒ ty))) → (acc : ST.Exp ctx ty) → (counter : ST.Exp ctx ST.TyNat) → Exp (map embedd-ST-Ty ctx) (embedd-ST-Ty ty)
embedd-ST-P {n} {ctx} {ty} h acc counter = 
          let h' =  (embedd-ST h) 
              acc' = embedd-ST acc
              counter' = embedd-ST counter 
              h'' = Lam (`case (Var zero) 
                  (`# ( weaken' (`𝟙 ∷ `𝟙 `+ (embedd-ST-Ty ty `× Nat) ∷ []) acc' ) (fold (ι₁ `0))) 
                  
                  (`# 
                      (App (App (weaken' (embedd-ST-Ty ty `× Nat ∷ `𝟙 `+ (embedd-ST-Ty ty `× Nat) ∷ []) h') (π₁ (Var zero))) (π₂ (Var zero)))  
                      (fold (ι₂(π₂ (Var zero))))))
              x = (P {n} {map embedd-ST-Ty ctx}  {G-Nat } {(embedd-ST-Ty ty) `×  Nat} h'') in 
         π₁(App x (  counter'  ))

embedd-ST {n} {ctx} (ST.Var f)  = Var f
embedd-ST (ST.Lam exp) = Lam (embedd-ST exp)
embedd-ST ST.CZero = fold (ι₁ `0)
embedd-ST ST.Suc = Lam (fold (ι₂ (Var zero)))
embedd-ST (ST.App f x) = App (embedd-ST f) (embedd-ST x)
-- embedd-ST {n} {ctx} {ty} (ST.PrecT h acc counter) = 
--         let h' =  (embedd-ST h) 
--             acc' = embedd-ST acc
--             counter' = embedd-ST counter 
--             h'' = Lam (`case (Var zero) 
--                   (`# ( weaken' (`𝟙 ∷ `𝟙 `+ (embedd-ST-Ty ty `× Nat) ∷ []) acc' ) (fold (ι₁ `0))) 
                  
--                   (`# 
--                       (App (App (weaken' (embedd-ST-Ty ty `× Nat ∷ `𝟙 `+ (embedd-ST-Ty ty `× Nat) ∷ []) h') (π₁ (Var zero))) (π₂ (Var zero)))  
--                       (π₂ (Var zero))))
--             x = (P {n} {map embedd-ST-Ty ctx}  {G-Nat } {(embedd-ST-Ty ty) `×  Nat} h'') in 
--          π₁(App x (  counter'  ))
embedd-ST {n} {ctx} {ty} (ST.PrecT h acc counter) = embedd-ST-P {n} {ctx} {ty} h acc counter 
embedd-ST (ST.Nat n) = ℕ→ExpNat n



embeddTyEval' : ∀ {ty : ST.Ty} →    ⟦ (embedd-ST-Ty ty) ⟧ᵀ → ST.evalTy ty
embeddTyEval : ∀ {ty : ST.Ty} →   ST.evalTy ty → ⟦ (embedd-ST-Ty ty) ⟧ᵀ 


embeddTyEval' {ST.TyNat} v = Nat→ℕ v
embeddTyEval' {(tyA ST.⇒ tyB)} v = λ x → embeddTyEval' {tyB} (v (embeddTyEval  {tyA} x)) 


embeddTyEval {ST.TyNat} v = ℕ→Nat v
embeddTyEval {(tyA ST.⇒ tyB)} v = λ x → embeddTyEval {tyB} (v (embeddTyEval' {tyA} x))





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

helper2 :  ∀  {tyA tyB : ST.Ty} (f : ST.evalTy (tyA ST.⇒ tyB)) (x : ST.evalTy tyA) →  embeddTyEval (f x) ≡  (embeddTyEval f) (embeddTyEval x)
helper2 {tyA} f x  rewrite embeddTyEval'∘embeddTyEval≡id x = refl


helper3 :  ∀  {tyA tyB tyC : ST.Ty} (f : ST.evalTy (tyA ST.⇒ (tyB ST.⇒ tyC))) (x : ST.evalTy tyA) (y : ST.evalTy tyB) →  embeddTyEval (f x y) ≡  (embeddTyEval f) (embeddTyEval x)(embeddTyEval y)
helper3 {tyA} f x y rewrite  embeddTyEval'∘embeddTyEval≡id x | embeddTyEval'∘embeddTyEval≡id y = refl














cong-app2 : ∀ {A B C : Set } {f g : A → B → C} →
           f ≡ g → (x : A) → (y : B) → f x y ≡ g x y
cong-app2 refl x y = refl


helper5 : ∀ {n}  {ctx : ST.Ctx n} {ty} → (ctx' : HVec ST.evalTy ctx) → (h  : ST.Exp ctx (ty ST.⇒ (ST.TyNat ST.⇒ ty))) → (acc : ST.Exp ctx ty) → (c : ℕ ) →  proj₁
  (foldF
  (λ x →
      eval
      (`case (Var zero)
      (`#
        (weakenGen [] [ `𝟙 , `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ]
        (map embedd-ST-Ty ctx) (embedd-ST acc))
        (fold (ι₁ `0)))
      (`#
        (App
        (App
          (weakenGen []
          [ embedd-ST-Ty ty `× ind (`𝟙 `+ `t) ,
          `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ]
          (map embedd-ST-Ty ctx) (embedd-ST h))
          (π₁ (Var zero)))
        (π₂ (Var zero)))
        (fold (ι₂ (π₂ (Var zero))))))
      (x ∷ᴴ mapᴴ' embeddTyEval ctx'))
  (ℕ→Nat c))
    ≡
  proj₁
  (PR-CC-ind-alt.mapFold `t (`𝟙 `+ `t)
  (λ x →
      eval
      (`case (Var zero)
      (`#
        (weakenGen [] [ `𝟙 , `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ]
        (map embedd-ST-Ty ctx) (embedd-ST acc))
        (fold (ι₁ `0)))
      (`#
        (App
        (App
          (weakenGen []
          [ embedd-ST-Ty ty `× ind (`𝟙 `+ `t) ,
          `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ]
          (map embedd-ST-Ty ctx) (embedd-ST h))
          (π₁ (Var zero)))
        (π₂ (Var zero)))
        (fold (ι₂ (π₂ (Var zero))))))
      (x ∷ᴴ mapᴴ' embeddTyEval ctx')
      )
  (ℕ→Nat c))
helper5 {n} {ctx} {ty} ctx' h acc zero = refl
helper5 {n} {ctx} {ty} ctx' h acc ( suc c) = refl



helper6 : ∀ {n}  {ctx : ST.Ctx n} {ty} → (ctx' : HVec ST.evalTy ctx) → (h  : ST.Exp ctx (ty ST.⇒ (ST.TyNat ST.⇒ ty))) → (acc : ST.Exp ctx ty) → (c : ℕ ) →  (ℕ→Nat c) ≡  (proj₂
       (PR-CC-ind-alt.mapFold `t (`𝟙 `+ `t)
        (λ x →
           eval
           (`case (Var zero)
            (`#
             (weakenGen [] [ `𝟙 , `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ]
              (map embedd-ST-Ty ctx) (embedd-ST acc))
             (fold (ι₁ `0)))
            (`#
             (App
              (App
               (weakenGen []
                [ embedd-ST-Ty ty `× ind (`𝟙 `+ `t) ,
                `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ]
                (map embedd-ST-Ty ctx) (embedd-ST h))
               (π₁ (Var zero)))
              (π₂ (Var zero)))
             (fold (ι₂ (π₂ (Var zero))))))
           (x ∷ᴴ mapᴴ' embeddTyEval ctx')
           )
        (ℕ→Nat c)))
helper6 {n} {ctx} {ty} ctx' h acc zero = refl
helper6 {n} {ctx} {ty} ctx' h acc (suc c) = cong fold (cong inj₂ (helper6 {n} {ctx} {ty} ctx' h acc c))

embedd-ST-sound : ∀ {n}  {ctx : ST.Ctx n} {ty} → (ctx' : HVec ST.evalTy ctx) → (sTExp : ST.Exp ctx ty)  → embeddTyEval {ty} ((ST.evalExp sTExp ctx') ) ≡  ( eval (embedd-ST sTExp) (mapᴴ' (embeddTyEval) ctx') ) 


helper4 : ∀ {n}  {ctx : ST.Ctx n} {ty} → (ctx' : HVec ST.evalTy ctx) → (h  : ST.Exp ctx (ty ST.⇒ (ST.TyNat ST.⇒ ty))) → (acc : ST.Exp ctx ty) → (c : ℕ ) → embeddTyEval
      (para (ST.evalExp h ctx') (ST.evalExp acc ctx') c)
      ≡
      proj₁
      (foldF
       (λ x →
          eval
          (`case (Var zero)
           (`#
            (weakenGen [] [ `𝟙 , `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ]
             (map embedd-ST-Ty ctx) (embedd-ST acc))
            (fold (ι₁ `0)))
           (`#
            (App
             (App
              (weakenGen []
               [ embedd-ST-Ty ty `× ind (`𝟙 `+ `t) ,
               `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ]
               (map embedd-ST-Ty ctx) (embedd-ST h))
              (π₁ (Var zero)))
             (π₂ (Var zero)))
            (fold (ι₂ (π₂ (Var zero))))    ))
          (x ∷ᴴ mapᴴ' embeddTyEval ctx')
          )
       (ℕ→Nat c))

       
helper4 ctx' h acc  zero rewrite embedd-ST-sound ctx' acc = sym (weaken'-Eq (tt ∷ᴴ (inj₁ tt ∷ᴴ  []ᴴ)) (mapᴴ' embeddTyEval ctx') (embedd-ST acc))
helper4 {n} {ctx} {ty} ctx' h acc  (suc c) rewrite weaken'-Eq {ctxB = [ embedd-ST-Ty ty `× ind (`𝟙 `+ `t) ,
       `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ] }{ctxC = map embedd-ST-Ty ctx}  ( PR-CC-ind-alt.mapFold `t (`𝟙 `+ `t)
       (λ x →
          eval
          (`case (Var zero)
           (`#
            (weakenGen [] [ `𝟙 , `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ]
             (map embedd-ST-Ty ctx) (embedd-ST acc))
            (fold (ι₁ `0)))
           (`#
            (App
             (App
              (weakenGen []
               [ embedd-ST-Ty ty `× ind (`𝟙 `+ `t) ,
               `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ]
               (map embedd-ST-Ty ctx) (embedd-ST h))
              (π₁ (Var zero)))
             (π₂ (Var zero)))
            (fold (ι₂(π₂ (Var zero))))))
          (x ∷ᴴ mapᴴ' embeddTyEval ctx')
          )
       (ℕ→Nat c) ∷ᴴ 
       
       (inj₂
        (PR-CC-ind-alt.mapFold `t (`𝟙 `+ `t)
         (λ x →
            eval
            (`case (Var zero)
             (`#
              (weakenGen [] [ `𝟙 , `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ]
               (map embedd-ST-Ty ctx) (embedd-ST acc))
              (fold (ι₁ `0)))
             (`#
              (App
               (App
                (weakenGen []
                 [ embedd-ST-Ty ty `× ind (`𝟙 `+ `t) ,
                 `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ]
                 (map embedd-ST-Ty ctx) (embedd-ST h))
                (π₁ (Var zero)))
               (π₂ (Var zero)))
              (fold (ι₂(π₂ (Var zero))))))
            (x ∷ᴴ mapᴴ' embeddTyEval ctx')
            )
         (ℕ→Nat c)) ∷ᴴ []ᴴ) ) (mapᴴ' embeddTyEval ctx') ((embedd-ST h)) | helper5 {n} {ctx} {ty} ctx' h acc c = 
         
          (embeddTyEval (ST.evalExp h ctx' (para (ST.evalExp h ctx') (ST.evalExp acc ctx') c) c)) 
              ≡⟨ helper3  (ST.evalExp h ctx') ((para (ST.evalExp h ctx') (ST.evalExp acc ctx') c)) c  ⟩ 
          ((embeddTyEval (ST.evalExp h ctx'))    (embeddTyEval ((para (ST.evalExp h ctx') (ST.evalExp acc ctx') c))) (embeddTyEval c) 
              ≡⟨ cong-app2 (embedd-ST-sound ctx' h) (embeddTyEval ((para (ST.evalExp h ctx') (ST.evalExp acc ctx') c))) (embeddTyEval c) ⟩ 
          eval (embedd-ST h) (mapᴴ' embeddTyEval ctx')(embeddTyEval (para (ST.evalExp h ctx') (ST.evalExp acc ctx') c))(ℕ→Nat c) 
              ≡⟨ cong₂ (eval (embedd-ST h) (mapᴴ' embeddTyEval ctx')) {u = (ℕ→Nat c)} {v = (ℕ→Nat c)}  (helper4 ctx' h acc c) refl  ⟩  
          eval (embedd-ST h) (mapᴴ' embeddTyEval ctx')
      (proj₁
       (foldF
        (λ x →
           eval
           (`case (Var zero)
            (`#
             (weakenGen [] [ `𝟙 , `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ]
              (map embedd-ST-Ty ctx) (embedd-ST acc))
             (fold (ι₁ `0)))
            (`#
             (App
              (App
               (weakenGen []
                [ embedd-ST-Ty ty `× ind (`𝟙 `+ `t) ,
                `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ]
                (map embedd-ST-Ty ctx) (embedd-ST h))
               (π₁ (Var zero)))
              (π₂ (Var zero)))
             (fold (ι₂ (π₂ (Var zero))))))
           (x ∷ᴴ mapᴴ' embeddTyEval ctx')
           )
        (ℕ→Nat c)))
      (ℕ→Nat c) 
                  ≡⟨ cong₂ (eval (embedd-ST h) (mapᴴ' embeddTyEval ctx')) (helper5 {n} {ctx} {ty} ctx' h acc c) ((helper6 {n} {ctx} {ty} ctx' h acc c))  ⟩ 
                  
      (eval (embedd-ST h) (mapᴴ' embeddTyEval ctx')
      (proj₁
       (PR-CC-ind-alt.mapFold `t (`𝟙 `+ `t)
        (λ x →
           eval
           (`case (Var zero)
            (`#
             (weakenGen [] [ `𝟙 , `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ]
              (map embedd-ST-Ty ctx) (embedd-ST acc))
             (fold (ι₁ `0)))
            (`#
             (App
              (App
               (weakenGen []
                [ embedd-ST-Ty ty `× ind (`𝟙 `+ `t) ,
                `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ]
                (map embedd-ST-Ty ctx) (embedd-ST h))
               (π₁ (Var zero)))
              (π₂ (Var zero)))
             (fold (ι₂ (π₂ (Var zero))))))
           (x ∷ᴴ mapᴴ' embeddTyEval ctx')
           )
        (ℕ→Nat c)))
      (proj₂
       (PR-CC-ind-alt.mapFold `t (`𝟙 `+ `t)
        (λ x →
           eval
           (`case (Var zero)
            (`#
             (weakenGen [] [ `𝟙 , `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ]
              (map embedd-ST-Ty ctx) (embedd-ST acc))
             (fold (ι₁ `0)))
            (`#
             (App
              (App
               (weakenGen []
                [ embedd-ST-Ty ty `× ind (`𝟙 `+ `t) ,
                `𝟙 `+ (embedd-ST-Ty ty `× ind (`𝟙 `+ `t)) ]
                (map embedd-ST-Ty ctx) (embedd-ST h))
               (π₁ (Var zero)))
              (π₂ (Var zero)))
             (fold (ι₂ (π₂ (Var zero))))))
           (x ∷ᴴ mapᴴ' embeddTyEval ctx')
           )
        (ℕ→Nat c)))) ∎ )



embedd-ST-sound  ( ctx') (ST.Var ( f)) = lookupMapᴴ f embeddTyEval ctx' 
embedd-ST-sound ctx' (ST.Lam exp) = extensionality (λ x → embedd-ST-sound (embeddTyEval' x ∷ᴴ ctx') exp)
embedd-ST-sound ctx' ST.CZero = refl
embedd-ST-sound ctx' ST.Suc = extensionality (λ x → cong fold (cong inj₂ (ℕ→Nat∘Nat→ℕ≡id x) ))
embedd-ST-sound {ty = ty} ctx' (ST.App f x) rewrite sym (embedd-ST-sound ctx' f) |  sym (embedd-ST-sound ctx' x) | embeddTyEval'∘embeddTyEval≡id (ST.evalExp x ctx') = refl 
embedd-ST-sound ctx' (ST.Nat x) = ℕ→Nat≡eval∘ℕ→ExpNat x ((mapᴴ' (embeddTyEval) ctx'))
embedd-ST-sound {n} {ctx} {ty} ctx' (ST.PrecT h acc counter) rewrite sym (embedd-ST-sound ctx' counter)  with ST.evalExp counter ctx'
... | c  =  helper4 ctx' h acc c
