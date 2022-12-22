\begin{code}[hide]
module PR-Nat-Example where

import Relation.Binary.PropositionalEquality as Eq
open Eq
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡˘; step-≡; _∎)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero; _+_; _*_; _^_; _∸_; pred; _≤_; z≤n; s≤s; _<_)
open import Data.Nat.Properties using (+-identityʳ; +-cancelʳ-≡; suc-injective; +-suc; +-comm; +-∸-assoc; ∸-+-assoc; 0∸n≡0; ≤-trans; ≤-refl; m≤n+m; m∸n+n≡m; m+n∸m≡n; m+n∸n≡m)
open import Data.Product using (Σ; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; _++_)
open import Agda.Builtin.Nat public
  using () renaming (_<_ to _<ᵇ_)

open import Utils

open import PR-Nat

----------------------------------------------------------------------
-- addition
\end{code}
\begin{code}
addP : PR 2
addP = P (π zero) (C σ [ π zero ])

addP=+ : ∀ m n → eval addP [ m , n ] ≡ m + n
addP=+ zero n = refl
addP=+ (suc m) n rewrite addP=+ m n = refl
\end{code}
\begin{code}[hide]
----------------------------------------------------------------------
-- multiplication

mulP : PR 2
mulP = P (C Z []) (C addP [ π (suc (suc zero)) , π zero ])

mulP=* : ∀ m n → eval mulP [ m , n ] ≡ m * n
mulP=* zero n = refl
mulP=* (suc m) n
  rewrite mulP=* m n
        | addP=+ n (m * n) = refl

----------------------------------------------------------------------
-- exponentiation

expP : PR 2
expP = C (P (C σ [ C Z [] ]) (C mulP [ π (suc (suc zero)) , π zero ])) [ π (suc zero) , π zero ]

expP=^ : ∀ m n → eval expP [ m , n ] ≡ m ^ n
expP=^ m zero = refl
expP=^ m (suc n)
  rewrite expP=^ m n
        | mulP=* m (m ^ n) = refl

----------------------------------------------------------------------
-- predecessor

predP : PR 1
predP = P Z (π (suc zero))

predP=∸1 : ∀ m → eval predP [ m ] ≡ pred m
predP=∸1 zero = refl
predP=∸1 (suc m) = refl

----------------------------------------------------------------------
-- subtraction (monus)

subP : PR 2
subP = C (P (π zero) (C predP [ π zero ])) [ π (suc zero) , π zero ]

m∸n∸1≡m∸sucn : ∀ m n → m ∸ n ∸ 1 ≡ m ∸ suc n
m∸n∸1≡m∸sucn zero zero = refl
m∸n∸1≡m∸sucn zero (suc n) = refl
m∸n∸1≡m∸sucn (suc m) zero = refl
m∸n∸1≡m∸sucn (suc m) (suc n) = m∸n∸1≡m∸sucn m n

subP=∸ : ∀ m n → eval subP [ m , n ] ≡ m ∸ n
subP=∸ m zero = refl
subP=∸ m (suc n)
  rewrite subP=∸ m n
        | predP=∸1 (m ∸ n) = m∸n∸1≡m∸sucn m n

----------------------------------------------------------------------
-- factorial

facP : PR 1
facP = P (C σ [ Z ]) (C mulP [ π zero , C σ [ π (suc zero) ] ])

fac : ℕ → ℕ
fac zero = 1
fac (suc n) = fac n * suc n

facP=fac : ∀ m → eval facP [ m ] ≡ fac m
facP=fac zero = refl
facP=fac (suc m)
  rewrite facP=fac m
        | mulP=* (fac m) (suc m) = refl

----------------------------------------------------------------------
-- auxiliary definitions for remainder

TRUE  = 1
FALSE = 0

isZeroP : PR 1
isZeroP = P (C σ [ C Z [] ]) (C Z [])

isZero : ℕ → ℕ
isZero zero = TRUE
isZero (suc n) = FALSE

isZeroP=isZero : ∀ m → eval isZeroP [ m ] ≡ isZero m
isZeroP=isZero zero = refl
isZeroP=isZero (suc m) = refl

--------------------

ifElseP : PR 3
ifElseP = P (π (suc zero)) (π (suc (suc zero)))

ifElse : ℕ → ℕ → ℕ → ℕ
ifElse zero n o = o
ifElse (suc m) n o = n

ifElseP=ifElse : ∀ m n o → eval ifElseP [ m , n , o ] ≡ ifElse m n o
ifElseP=ifElse zero n o = refl
ifElseP=ifElse (suc m) n o = refl

--------------------

notP : PR 1
notP = isZeroP

toBoolP : PR 1
toBoolP = P Z (C σ [ C Z [] ])

data _~_ : ℕ → ℕ → Set where
  FF : zero ~ zero
  TT : ∀{m} → suc m ~ 1

toBool~ : ∀ m n → m ~ n → eval toBoolP [ m ] ≡ n
toBool~ .0 .0 FF = refl
toBool~ .(suc _) .1 TT = refl

toBoolP′ : PR 1
toBoolP′ = C notP [ notP ]

toBoolP=toBoolP′ : ∀ m → eval toBoolP [ m ] ≡ eval toBoolP′ [ m ]
toBoolP=toBoolP′ zero = refl
toBoolP=toBoolP′ (suc m) = refl

--------------------

smallerP : PR 2
smallerP = C toBoolP [ subP ]

smaller : ℕ → ℕ → ℕ
smaller m n with n <ᵇ m
... | false = FALSE
... | true = TRUE

subP~smaller : ∀ m n → (m ∸ n) ~ smaller m n
subP~smaller zero n rewrite 0∸n≡0 n = FF
subP~smaller (suc m) zero = TT
subP~smaller (suc m) (suc n)
  with subP~smaller m n
... | ih with n <ᵇ m
... | false = ih
... | true = ih

smallerP=smaller : ∀ m n → eval smallerP [ m , n ] ≡ smaller m n
smallerP=smaller m n rewrite subP=∸ m n = toBool~ (m ∸ n) (smaller m n) (subP~smaller m n)

-- rem m n = m % n
remGP : PR 3
remGP = C ifElseP [ C smallerP [ π (suc (suc zero)) , C σ [ π zero ] ]
                  , C σ [ π zero ]
                  , C Z [] ]

remP : PR 2
remP = P (C Z []) remGP

-- inefficent, but unclear how to handle Nat.DivMod._%_
rem : ℕ → ℕ → ℕ
rem zero n = 0
rem (suc m) n with rem m n
... | m%n with suc m%n <ᵇ n
... | false = 0
... | true = suc m%n

remP=rem : ∀ m n → eval remP [ m , n ] ≡ rem m n
remP=rem zero n = refl
remP=rem (suc m) n
  rewrite remP=rem m n
  rewrite smallerP=smaller n (suc (rem m n))
  with suc (rem m n) <ᵇ n
... | false = refl
... | true = refl

----------------------------------------------------------------------
-- pairing

triangle : ℕ → ℕ
triangle zero = 0
triangle (suc n) = suc n + triangle n

triangleP : PR 1
triangleP = P Z (C addP [ C σ [ π (suc zero) ] , π zero ])

triangleP=triangle : ∀ n → eval triangleP [ n ] ≡ triangle n
triangleP=triangle zero = refl
triangleP=triangle (suc n)
  rewrite triangleP=triangle n = addP=+ (suc n) (triangle n)

mkpair : ℕ → ℕ → ℕ
mkpair x y = triangle (x + y) + y

mkpairP : PR 2
mkpairP = C addP [ C triangleP [ (C addP [ π zero , π (suc zero) ]) ] , π (suc zero) ]

mkpairP=mkpair : ∀ m n → eval mkpairP [ m , n ] ≡ mkpair m n
mkpairP=mkpair m n
  rewrite addP=+ m n
        | triangleP=triangle (m + n)
        | addP=+ (triangle (m + n)) n = refl

----------------------------------------------------------------------
-- unpairing

toBool : ℕ → ℕ
toBool zero = 0
toBool (suc n) = 1

toBoolP=toBool : ∀ m → eval toBoolP [ m ] ≡ toBool m
toBoolP=toBool zero = refl
toBoolP=toBool (suc m) = refl

not : ℕ → ℕ
not zero = 1
not (suc n) = 0

notP=not : ∀ m → eval notP [ m ] ≡ not m
notP=not zero = refl
notP=not (suc m) = refl

equal : ℕ → ℕ → ℕ
equal m n = not ((m ∸ n) + (n ∸ m))

equalP : PR 2
equalP = C notP [ (C addP [ (C subP [ π zero , π (suc zero) ]) , (C subP [ π (suc zero) , π zero ]) ]) ]

equalP=equal : ∀ m n → eval equalP [ m , n ] ≡ equal m n
equalP=equal m n
  rewrite subP=∸ m n
        | subP=∸ n m
        | addP=+ (m ∸ n) (n ∸ m) = notP=not (m ∸ n + (n ∸ m))

-- check stdlib

m∸m≡0 : ∀ m → m ∸ m ≡ 0
m∸m≡0 zero = refl
m∸m≡0 (suc m) = m∸m≡0 m

m∸n≡0⇒m≤n : ∀ m n → m ∸ n ≡ 0 → m ≤ n
m∸n≡0⇒m≤n zero n m∸n≡0 = z≤n
m∸n≡0⇒m≤n (suc m) (suc n) m∸n≡0 = s≤s (m∸n≡0⇒m≤n m n m∸n≡0)

n≤suc-n : ∀ n → n ≤ suc n
n≤suc-n zero = z≤n
n≤suc-n (suc n) = s≤s (n≤suc-n n)

n≤m-≡/sucn≤m : ∀ n m → n ≤ m → n ≡ m ⊎ suc n ≤ m
n≤m-≡/sucn≤m .zero zero z≤n = inj₁ refl
n≤m-≡/sucn≤m .zero (suc m) z≤n = inj₂ (s≤s z≤n)
n≤m-≡/sucn≤m .(suc _) .(suc _) (s≤s n≤m)
  with n≤m-≡/sucn≤m _ _ n≤m
... | inj₁ refl = inj₁ refl
... | inj₂ sucm≤n = inj₂ (s≤s sucm≤n)


≤-antisymm : ∀ m n → m ≤ n → n ≤ m → m ≡ n
≤-antisymm .zero .zero z≤n z≤n = refl
≤-antisymm .(suc _) .(suc _) (s≤s m≤n) (s≤s n≤m)
  rewrite ≤-antisymm _ _ m≤n n≤m = refl

≡-≤ : ∀ {m n : ℕ} → m ≡ n → m ≤ n
≡-≤ refl = ≤-refl

-- check stdlib end

≡-equal : ∀ m n → m ≡ n → equal m n ≡ 1
≡-equal m .m refl rewrite m∸m≡0 m = refl

equal-≡ : ∀ m n → equal m n ≡ 1 → m ≡ n
equal-≡ m n eql-mn-1
  with m ∸ n in m∸n≡0
... | zero
  with n ∸ m in n∸m≡0
... | zero
  = ≤-antisymm m n (m∸n≡0⇒m≤n m n m∸n≡0) (m∸n≡0⇒m≤n n m n∸m≡0)

1≢0 : 1 ≢ 0
1≢0 ()

equal-≢ : ∀ m n → equal m n ≡ 0 → m ≢ n
equal-≢ m .m eql-mn-0 refl
  with ≡-equal m m refl
... | eq rewrite eq = ⊥-elim (1≢0 eql-mn-0)

not<2 : ∀ m → not m < 2
not<2 zero = s≤s (s≤s z≤n)
not<2 (suc m) = s≤s z≤n

equal<2 : ∀ m n → equal m n < 2
equal<2 m n = not<2 ((m ∸ n) + (n ∸ m))

¬not>1 : ∀ m k → not m ≡ suc (suc k) → ⊥
¬not>1 zero k ()
¬not>1 (suc m) k ()

≢-equal : ∀ m n → m ≢ n → equal m n ≡ 0
≢-equal m n m≢n
  with equal m n in eq-mn
... | zero = refl
... | suc (suc r) = ⊥-elim (¬not>1 _ _ eq-mn)
... | suc zero with equal-≡ m n eq-mn
... | refl = ⊥-elim (m≢n refl)

-- m = untriangle n → triangle m ≤ n /\ n < triangle (suc m)
untriangle : ℕ → ℕ
untriangle zero = 0
untriangle (suc n) = equal (triangle (suc (untriangle n))) (suc n) + untriangle n

-- i          = 0 1 2 3  4  5
-- triangle i = 0 1 3 6 10 15

-- n   = 0 1 2 3 4 5 6 7 8 9 10
-- u n = 0 1 1 2 2 2 3 3 3 3

module untriangle-tests where
  _ : untriangle 0 ≡ 0
  _ = refl
  _ : untriangle 1 ≡ 1
  _ = refl
  _ : untriangle 2 ≡ 1
  _ = refl
  _ : untriangle 3 ≡ 2
  _ = refl
  _ : untriangle 4 ≡ 2
  _ = refl
  _ : untriangle 5 ≡ 2
  _ = refl
  _ : untriangle 6 ≡ 3
  _ = refl

untriangleP : PR 1
untriangleP = P Z (C addP [ C equalP [ (C triangleP [ (C σ [ π zero ]) ]) , C σ [ π (suc zero) ] ] , π zero ])

untriangleP=untriangle : ∀ n → eval untriangleP [ n ] ≡ untriangle n
untriangleP=untriangle zero = refl
untriangleP=untriangle (suc n)
  with untriangleP=untriangle n
... | ih =
  begin
    eval untriangleP [ suc n ]
    ≡⟨⟩
      eval addP [ eval equalP [ eval triangleP [ suc (eval untriangleP [ n ]) ] , suc n ] , eval untriangleP [ n ] ]
    ≡⟨ cong (λ m → eval addP [ eval equalP [ eval triangleP [ suc m ] , suc n ] , m ]) ih ⟩
      eval addP [ eval equalP [ eval triangleP [ suc (untriangle n) ] , suc n ] , untriangle n ]
    ≡⟨ cong (λ m → eval addP [ eval equalP [ m , suc n ] , untriangle n ]) (triangleP=triangle (suc (untriangle n))) ⟩
      eval addP [ eval equalP [ triangle (suc (untriangle n)) , suc n ] , untriangle n ]
    ≡⟨ cong (λ m → eval addP [ m , untriangle n ]) (equalP=equal (triangle (suc (untriangle n))) (suc n)) ⟩
      eval addP [ equal (triangle (suc (untriangle n))) (suc n) , untriangle n ]
    ≡⟨ addP=+ (equal (triangle (suc (untriangle n))) (suc n)) (untriangle n) ⟩
      equal (triangle (suc (untriangle n))) (suc n) + untriangle n
    ≡⟨⟩
      untriangle (suc n)
    ∎

untriangle-spec : ℕ → ℕ → Set
untriangle-spec m n = m ≡ untriangle n → triangle m ≤ n × n < triangle (suc m)

-- triangle (untriangle n) ≤ n × n < triangle (suc (untriangle n))

untriangle-spec-holds : ∀ m n → untriangle-spec m n
untriangle-spec-holds .(untriangle zero) zero refl = ⟨ z≤n , s≤s z≤n ⟩
untriangle-spec-holds .(untriangle (suc n)) (suc n) refl
  with untriangle-spec-holds (untriangle n) n refl
... | ⟨ tr-untr-n≤n , s≤s n≤un-n+tr-un-n ⟩
  with equal (triangle (suc (untriangle n))) (suc n) in eqlr
... | suc zero = ⟨ ≡-≤ (equal-≡ (triangle (suc (untriangle n))) (suc n) eqlr)
                 , s≤s (s≤s (≤-trans n≤un-n+tr-un-n (≤-trans (m≤n+m (untriangle n + triangle (untriangle n)) (suc (untriangle n))) (≡-≤ (sym (+-suc (untriangle n) _)))))) ⟩
... | suc (suc r) = ⊥-elim (¬not>1 _ _ eqlr)
... | zero
  with n≤m-≡/sucn≤m n (untriangle n + triangle (untriangle n)) n≤un-n+tr-un-n
... | inj₁ x = ⊥-elim (equal-≢ (triangle (suc (untriangle n))) (suc n) eqlr (cong suc (sym x)))
... | inj₂ suc-n≤un-n+tr-un-n = ⟨ (≤-trans tr-untr-n≤n (n≤suc-n n)) , s≤s suc-n≤un-n+tr-un-n ⟩


triangle-prop : ∀ m → m + triangle m ≡ triangle (suc m) ∸ 1
triangle-prop zero = refl
triangle-prop (suc m) = refl

triangle-prop1 : ∀ m → suc m + triangle m ≡ triangle (suc m)
triangle-prop1 m = refl

-- properties of untriangle ∘ triangle

untriangle-triangle : ∀ m y → y ≤ m → untriangle (y + triangle m) ≡ m
untriangle-triangle zero .zero z≤n = refl
untriangle-triangle (suc m) zero y≤m =
  begin
    untriangle (triangle (suc m))
  ≡⟨⟩
    untriangle (suc m + triangle m)
  ≡⟨⟩
    equal (triangle (suc (untriangle (m + triangle m)))) (suc m + triangle m) + untriangle (m + triangle m)
  ≡⟨ cong (λ r → equal (triangle (suc r)) (suc m + triangle m) + r) (untriangle-triangle m m ≤-refl) ⟩
    equal (triangle (suc m)) (suc m + triangle m) + m
  ≡⟨ cong (_+ m) (≡-equal (triangle (suc m)) (suc m + triangle m) refl) ⟩
    refl
untriangle-triangle (suc m) (suc y) (s≤s y≤m) =
  begin
    untriangle (suc y + triangle (suc m))
  ≡⟨⟩
    untriangle (suc y + (suc m + triangle m))
  ≡⟨⟩
    equal (triangle (suc (untriangle (y + triangle (suc m))))) (suc y + (suc m + triangle m)) + untriangle (y + triangle (suc m))
  ≡⟨ cong (λ ih → equal (triangle (suc ih)) (suc y + (suc m + triangle m)) + ih) (untriangle-triangle (suc m) y (≤-trans y≤m (n≤suc-n m))) ⟩
    equal ((suc (suc m)) + triangle (suc m)) (suc y + triangle (suc m)) + (suc m)
  ≡⟨ cong (_+ suc m) (not-equal (suc m) (suc y) (s≤s y≤m)) ⟩
    suc m
  ∎
  where
    -- -- +-cancelˡ-≡
    -- lemma-0 : ∀ a b c → a + b ≡ a + c → b ≡ c
    -- lemma-0 zero b c ab≡ac = ab≡ac
    -- lemma-0 (suc a) b c ab≡ac = lemma-0 a b c (suc-injective ab≡ac)

    -- -- +-cancelʳ-≡
    -- lemma-0′ : ∀ a b c → b + a ≡ c + a → b ≡ c
    -- lemma-0′ a b c ba≡ca = lemma-0 a b c (trans (+-comm a b) (trans ba≡ca (+-comm c a)))

    lemma : ∀ m y → suc m + triangle m ≡ y + triangle m → suc m ≡ y
    lemma m y = +-cancelʳ-≡ (suc m) y

    lemma-contra : ∀ m y → suc m ≢ y → suc m + triangle m ≢ y + triangle m
    lemma-contra m y sm≢y smt≡yt = sm≢y (lemma m y smt≡yt)

    y≤m⇒sm≢y : ∀ y m → y ≤ m → suc m ≢ y
    y≤m⇒sm≢y .zero m z≤n = λ ()
    y≤m⇒sm≢y (suc y) (suc m) (s≤s y≤m) = λ{ refl → y≤m⇒sm≢y y m y≤m refl }

    not-equal : ∀ m y → y ≤ m → equal ((suc m) + triangle m) (y + triangle m) ≡ 0
    not-equal m y y≤m = ≢-equal ((suc m) + triangle m) (y + triangle m) (lemma-contra m y (y≤m⇒sm≢y y m y≤m))
    

unpair-y : ℕ → ℕ
unpair-y p = p ∸ triangle (untriangle p)

unpair-x : ℕ → ℕ
unpair-x p = untriangle p ∸ unpair-y p

-- pair/unpair is an isomorphism

pair-unpair-identity : ∀ p → mkpair (unpair-x p) (unpair-y p) ≡ p
pair-unpair-identity p =
  begin
    mkpair (unpair-x p) (unpair-y p)
  ≡⟨⟩
    triangle (unpair-x p + unpair-y p) + unpair-y p
  ≡⟨⟩
    triangle (untriangle p ∸ (p ∸ triangle (untriangle p)) + (p ∸ triangle (untriangle p))) + (p ∸ triangle (untriangle p))
  ≡⟨ cong (λ m → triangle m + (p ∸ triangle (untriangle p))) (m∸n+n≡m (lemma1 p)) ⟩
    triangle (untriangle p) + (p ∸ triangle (untriangle p))
  ≡˘⟨ +-∸-assoc (triangle (untriangle p)) (lemma2 p) ⟩
    (triangle (untriangle p) + p) ∸ triangle (untriangle p)
  ≡⟨ m+n∸m≡n (triangle (untriangle p)) p ⟩
    p
  ∎
  where
    lemma1 : ∀ p → p ∸ triangle (untriangle p) ≤ untriangle p
    lemma1 p = {!!}
    lemma2 : ∀ n → triangle (untriangle n) ≤ n
    lemma2 n = proj₁ (untriangle-spec-holds (untriangle n) n refl)

un-tr-x+y : ∀ x y → untriangle (triangle (x + y) + y) ≡ x + y
un-tr-x+y x y = trans (cong untriangle (+-comm (triangle (x + y)) y)) (untriangle-triangle (x + y) y (m≤n+m y x))

unpair-pair-identity-y : ∀ x y → unpair-y (mkpair x y) ≡ y
unpair-pair-identity-y x y =
  begin
    unpair-y (mkpair x y)
  ≡⟨⟩
    unpair-y (triangle (x + y) + y)
  ≡⟨⟩
    (triangle (x + y) + y) ∸ triangle (untriangle (triangle (x + y) + y))
  ≡⟨ cong (λ m → triangle (x + y) + y ∸ triangle m) (un-tr-x+y x y) ⟩
    triangle (x + y) + y ∸ triangle (x + y)
  ≡⟨ m+n∸m≡n (triangle (x + y)) y ⟩
    y
  ∎
    

unpair-pair-identity-x : ∀ x y → unpair-x (mkpair x y) ≡ x
unpair-pair-identity-x x y =
  begin
    unpair-x (mkpair x y)
  ≡⟨⟩
    untriangle (mkpair x y) ∸ unpair-y (mkpair x y)
  ≡⟨ cong (untriangle (mkpair x y) ∸_) (unpair-pair-identity-y x y) ⟩
    untriangle (mkpair x y) ∸ y
  ≡⟨⟩
    untriangle (triangle (x + y) + y) ∸ y
  ≡⟨ cong (_∸ y) (un-tr-x+y x y) ⟩
    x + y ∸ y
  ≡⟨ m+n∸n≡m x y ⟩
    x
  ∎

-- primitive recursive encoding

unpair-yP : PR 1
unpair-yP = C subP [ π zero , C triangleP [ untriangleP ] ]

unpair-xP : PR 1
unpair-xP = C subP [ untriangleP , unpair-yP ]

unpair-yP=unpair-y : ∀ p → eval unpair-yP [ p ] ≡ unpair-y p
unpair-yP=unpair-y p
  rewrite untriangleP=untriangle p
        | triangleP=triangle (untriangle p)
        | subP=∸ p (triangle (untriangle p))
  = refl

unpair-xP=unpair-x : ∀ p → eval unpair-xP [ p ] ≡ unpair-x p
unpair-xP=unpair-x p
  rewrite untriangleP=untriangle p 
        | triangleP=triangle (untriangle p)
        | subP=∸ p (triangle (untriangle p))
        | subP=∸ (untriangle p) (p ∸ (triangle (untriangle p)))
  = refl
\end{code}
