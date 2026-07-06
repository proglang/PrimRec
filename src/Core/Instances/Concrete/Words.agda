{-# OPTIONS --safe #-}

module Core.Instances.Concrete.Words where

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List) renaming ([] to []ᴸ; _∷_ to _∷ᴸ_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_; replicate)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans)

import PR-Words as Source
open import Core.PRFO
open import Core.Finite
open import Core.Semantics.Inductive using (paraGo)
open import Core.Instances.Common
open import Core.Instances.Words
open import Core.Instances.Concrete.Evaluator
open import Core.Instances.Concrete.Supported
open import Core.Instances.Concrete.Casts using (mapSem)

flatLetterF : (k : ℕ) → Flat (LetterF k)
flatLetterF zero = flat-𝟘
flatLetterF (suc k) = flat-+ (flatVec 1 flat-`) (flatLetterF k)

flatWordF : (k : ℕ) → Flat (WordF k)
flatWordF k = flat-+ flat-𝟙 (flatLetterF k)

supported-injectLetterAt : ∀ {k T} (a : Fin k) →
  Supported (injectLetterAt {T = T} a)
supported-injectLetterAt {suc k} zero = s-ι₁
supported-injectLetterAt {suc k} (suc a) =
  s-C s-ι₂ (supported-injectLetterAt a)

supported-injectLetter : ∀ {k T} (a : Fin k) →
  Supported (injectLetter {T = T} a)
supported-injectLetter a = s-C s-ι₂ (supported-injectLetterAt a)

supported-emptyCon : ∀ {k} → Supported (emptyCon {k})
supported-emptyCon {k} = s-C (s-con (flatWordF k)) s-ι₁

supported-letterCon : ∀ {k} (a : Fin k) → Supported (letterCon a)
supported-letterCon {k} a =
  s-C (s-con (flatWordF k)) (supported-injectLetter a)

supported-caseLettersAt : ∀ {k T U V}
  {handlers : (a : Fin k) → vec T 1 `× U →ᴾ V} →
  ((a : Fin k) → Supported (handlers a)) →
  Supported (caseLettersAt handlers)
supported-caseLettersAt {zero} supported-handlers = s-C s-⊥ s-π₁
supported-caseLettersAt {suc k} supported-handlers =
  s-C
    (s-case (supported-handlers zero)
      (supported-caseLettersAt (λ a → supported-handlers (suc a))))
    s-dist

caseLetters-inject : ∀ {k T U V}
  {handlers : (a : Fin k) → vec T 1 `× U →ᴾ V}
  (supported-handlers : (a : Fin k) → Supported (handlers a))
  (a : Fin k) (child : Sem (vec T 1)) (parameters : Sem U) →
  eval (supported-caseLettersAt supported-handlers)
    (eval (supported-injectLetterAt {T = T} a) child , parameters) ≡
  eval (supported-handlers a) (child , parameters)
caseLetters-inject {suc k} supported-handlers zero child parameters = refl
caseLetters-inject {suc k} supported-handlers (suc a) child parameters =
  caseLetters-inject (λ i → supported-handlers (suc i)) a child parameters

fmap-injectLetterAt : ∀ {k T U} (a : Fin k)
  (f : Sem T → Sem U) (child : Sem (vec T 1)) →
  fmapFlat (flatLetterF k) f
    (eval (supported-injectLetterAt {T = T} a) child) ≡
  eval (supported-injectLetterAt {T = U} a)
    (mapSem {T = T} {U = U} f 1 child)
fmap-injectLetterAt {suc k} {T} {U} zero f (child , tt) = refl
fmap-injectLetterAt {suc k} {T} {U} (suc a) f child =
  cong inj₂ (fmap-injectLetterAt {T = T} {U = U} a f child)

fmap-injectLetter : ∀ {k T U} (a : Fin k)
  (f : Sem T → Sem U) (child : Sem (vec T 1)) →
  fmapFlat (flatWordF k) f
    (eval (supported-injectLetter {T = T} a) child) ≡
  eval (supported-injectLetter {T = U} a)
    (mapSem {T = T} {U = U} f 1 child)
fmap-injectLetter {T = T} {U = U} a f child =
  cong inj₂ (fmap-injectLetterAt {T = T} {U = U} a f child)

supported : ∀ {k n} (p : Source.PR (Fin k) n) → Supported (compile p)
supported* : ∀ {k m n} (ps : Vec (Source.PR (Fin k) n) m) →
             Supported (compile* ps)
supported-wordParaHandlerᴾ : ∀ {k n}
  {g : vec (Word k) n →ᴾ Word k}
  {h : Fin k → vec (Word k) (2 + n) →ᴾ Word k} →
  Supported g → ((a : Fin k) → Supported (h a)) →
  Supported (wordParaHandlerᴾ g h)
supported-wordParaHandlerᴾ {k} {n} sg sh =
  s-C
    (s-case (s-C sg s-π₂)
      (supported-caseLettersAt λ a →
        s-C (sh a) (supported-preparePara 1 n)))
    s-dist

supported-wordParaHandler : ∀ {k n} (g : Source.PR (Fin k) n)
  (h : Fin k → Source.PR (Fin k) (2 + n)) →
  Supported (wordParaHandler g h)
supported-wordParaHandler g h =
  supported-wordParaHandlerᴾ (supported g) (λ a → supported (h a))

para-letterᴾ : ∀ {k n}
  {g : vec (Word k) n →ᴾ Word k}
  {h : Fin k → vec (Word k) (2 + n) →ᴾ Word k}
  (sg : Supported g) (sh : (a : Fin k) → Supported (h a))
  (a : Fin k) (child : Sem (Word k))
  (parameters : Sem (vec (Word k) n)) →
  paraGo
    (paraAlgebra {G = WordF k} {T = Word k} {U = vec (Word k) n}
      (flatWordF k) (eval (supported-wordParaHandlerᴾ sg sh)) parameters)
    (eval (supported-letterCon a) (child , tt)) (λ ())
  ≡
  eval (sh a)
    (paraFlat {G = WordF k} {T = Word k} {U = vec (Word k) n}
       (flatWordF k) (eval (supported-wordParaHandlerᴾ sg sh))
       (child , parameters) ,
     child , parameters)
para-letterᴾ {k} {n} {g} {h} sg sh a child parameters =
  trans
    (para-conFlat-β {G = WordF k} {T = Word k}
      {U = vec (Word k) n} (flatWordF k) handlerSem
      (eval (supported-injectLetter a) (child , tt)) parameters)
    (trans
      (cong handlerSem
        (cong (λ layer → layer , parameters)
          (trans
            (paraStep-as-fmap {G = WordF k} {T = Word k}
              {U = vec (Word k) n} (flatWordF k)
              handlerSem parameters
              (eval (supported-injectLetter a) (child , tt)))
            (fmap-injectLetter {T = Word k} {U = Word k `× Word k}
              a step (child , tt)))))
      (caseLetters-inject supported-handlers a
        ((recur child , child) , tt) parameters))
  where
  handlerSem :
    Sem ((WordF k [ Word k `× Word k ]) `× vec (Word k) n) →
    Sem (Word k)
  handlerSem = eval (supported-wordParaHandlerᴾ sg sh)

  recur : Sem (Word k) → Sem (Word k)
  recur x = paraFlat {G = WordF k} {T = Word k}
    {U = vec (Word k) n} (flatWordF k) handlerSem (x , parameters)

  step : Sem (Word k) → Sem (Word k `× Word k)
  step x = recur x , x

  supported-handlers : (i : Fin k) →
    Supported (C (h i) (preparePara 1 n))
  supported-handlers i = s-C (sh i) (supported-preparePara 1 n)

para-letter : ∀ {k n} (g : Source.PR (Fin k) n)
  (h : Fin k → Source.PR (Fin k) (2 + n))
  (a : Fin k) (child : Sem (Word k))
  (parameters : Sem (vec (Word k) n)) →
  paraGo
    (paraAlgebra {G = WordF k} {T = Word k} {U = vec (Word k) n}
      (flatWordF k) (eval (supported-wordParaHandler g h)) parameters)
    (eval (supported-letterCon a) (child , tt)) (λ ())
  ≡
  eval (supported (h a))
    (paraFlat {G = WordF k} {T = Word k} {U = vec (Word k) n}
       (flatWordF k) (eval (supported-wordParaHandler g h))
       (child , parameters) ,
     child , parameters)
para-letter {k} {n} g h a child parameters =
  para-letterᴾ (supported g) (λ i → supported (h i))
    a child parameters

supported Source.Z = supported-emptyCon
supported (Source.σ a) = supported-letterCon a
supported (Source.π i) = supported-lookup i
supported (Source.C f fs) = s-C (supported f) (supported* fs)
supported {k} {n = suc n} (Source.Pr g h) =
  s-Pr (WordF k) (flatWordF k) (supported-wordParaHandler g h)

supported* [] = s-⊤
supported* (p ∷ ps) = s-# (supported p) (supported* ps)

data Related {k : ℕ} : Sem (Word k) → List (Fin k) → Set where
  related-[] : Related (eval (supported-emptyCon {k}) tt) []ᴸ
  related-∷ : ∀ {a child xs} → Related child xs →
    Related (eval (supported-letterCon a) (child , tt)) (a ∷ᴸ xs)

data Related* {k : ℕ} : (n : ℕ) →
  Sem (vec (Word k) n) → Vec (List (Fin k)) n → Set where
  related-v[] : Related* zero tt []
  related-v∷ : ∀ {k x xs y ys} → Related x y → Related* k xs ys →
    Related* (suc k) (x , xs) (y ∷ ys)

lookup-related : ∀ {k n} (i : Fin n) {values : Sem (vec (Word k) n)}
  {xs : Vec (List (Fin k)) n} →
  Related* n values xs → Related (eval (supported-lookup i) values) (Data.Vec.lookup xs i)
lookup-related zero (related-v∷ rx rxs) = rx
lookup-related (suc i) (related-v∷ rx rxs) = lookup-related i rxs

correct : ∀ {k n} (p : Source.PR (Fin k) n)
  {values : Sem (vec (Word k) n)} {xs : Vec (List (Fin k)) n} →
  Related* n values xs → Related (eval (supported p) values) (Source.eval p xs)
correct* : ∀ {k m n} (ps : Vec (Source.PR (Fin k) n) m)
  {values : Sem (vec (Word k) n)} {xs : Vec (List (Fin k)) n} →
  Related* n values xs →
  Related* m (eval (supported* ps) values) (Source.eval* ps xs)

correct {k} Source.Z related-v[] = related-[] {k = k}
correct (Source.σ a) (related-v∷ child related-v[]) = related-∷ child
correct (Source.π i) related = lookup-related i related
correct (Source.C f fs) related = correct f (correct* fs related)
correct {k} {n = suc n} (Source.Pr g h)
  {values = tree , values} {xs = x ∷ xs}
  (related-v∷ first parameters) = go first
  where
  handler : Supported
    (wordParaHandler g h)
  handler = supported-wordParaHandler g h

  go : ∀ {tree′ word} → Related {k} tree′ word →
    Related
      (paraGo
        (paraAlgebra {G = WordF k} {T = Word k} {U = vec (Word k) n}
          (flatWordF k) (eval handler) values)
        tree′ (λ ()))
      (Source.eval (Source.Pr g h) (word ∷ xs))
  go related-[] = correct g parameters
  go (related-∷ {a = a} {child = childValue} {xs = childWord} child) =
    Eq.subst
      (λ target → Related target
        (Source.eval (Source.Pr g h) ((a ∷ᴸ childWord) ∷ xs)))
      (Eq.sym (para-letter g h a childValue values))
      (correct (h a)
        (related-v∷ (go child) (related-v∷ child parameters)))

correct* [] related = related-v[]
correct* (p ∷ ps) related = related-v∷ (correct p related) (correct* ps related)

----------------------------------------------------------------------
-- Concrete correctness for an arbitrary finitely presented alphabet
----------------------------------------------------------------------

module ForFinite {A : Set} (finiteA : Finite A) where
  module W = Core.Instances.Words.For finiteA

  k : ℕ
  k = size finiteA

  supportedFinite : ∀ {n} (p : Source.PR A n) →
    Supported (W.compileFinite p)
  supportedFinite* : ∀ {m n} (ps : Vec (Source.PR A n) m) →
    Supported (W.compileFinite* ps)

  supportedFinite Source.Z = supported-emptyCon
  supportedFinite (Source.σ a) = supported-letterCon (encode finiteA a)
  supportedFinite (Source.π i) = supported-lookup i
  supportedFinite (Source.C f fs) =
    s-C (supportedFinite f) (supportedFinite* fs)
  supportedFinite (Source.Pr g h) =
    s-Pr (WordF k) (flatWordF k)
      (supported-wordParaHandlerᴾ
        (supportedFinite g)
        (λ i → supportedFinite (h (decode finiteA i))))

  supportedFinite* [] = s-⊤
  supportedFinite* (p ∷ ps) =
    s-# (supportedFinite p) (supportedFinite* ps)

  data RelatedFinite : Sem (Word k) → List A → Set where
    related-[] : RelatedFinite (eval (supported-emptyCon {k}) tt) []ᴸ
    related-∷ : ∀ {a child xs} → RelatedFinite child xs →
      RelatedFinite
        (eval (supported-letterCon (encode finiteA a)) (child , tt))
        (a ∷ᴸ xs)

  data RelatedFinite* : (n : ℕ) →
    Sem (vec (Word k) n) → Vec (List A) n → Set where
    related-v[] : RelatedFinite* zero tt []
    related-v∷ : ∀ {n x xs y ys} →
      RelatedFinite x y → RelatedFinite* n xs ys →
      RelatedFinite* (suc n) (x , xs) (y ∷ ys)

  finiteLookupRelated : ∀ {n} (i : Fin n)
    {values : Sem (vec (Word k) n)} {xs : Vec (List A) n} →
    RelatedFinite* n values xs →
    RelatedFinite (eval (supported-lookup i) values) (Data.Vec.lookup xs i)
  finiteLookupRelated zero (related-v∷ x xs) = x
  finiteLookupRelated (suc i) (related-v∷ x xs) = finiteLookupRelated i xs

  correctFinite : ∀ {n} (p : Source.PR A n)
    {values : Sem (vec (Word k) n)} {xs : Vec (List A) n} →
    RelatedFinite* n values xs →
    RelatedFinite (eval (supportedFinite p) values) (Source.eval p xs)
  correctFinite* : ∀ {m n} (ps : Vec (Source.PR A n) m)
    {values : Sem (vec (Word k) n)} {xs : Vec (List A) n} →
    RelatedFinite* n values xs →
    RelatedFinite* m (eval (supportedFinite* ps) values) (Source.eval* ps xs)

  correctFinite Source.Z related-v[] = related-[]
  correctFinite (Source.σ a) (related-v∷ child related-v[]) =
    related-∷ child
  correctFinite (Source.π i) related = finiteLookupRelated i related
  correctFinite (Source.C f fs) related =
    correctFinite f (correctFinite* fs related)
  correctFinite {n = suc n} (Source.Pr g h)
    {values = tree , values} {xs = x ∷ xs}
    (related-v∷ first parameters) = go first
    where
    sg = supportedFinite g
    sh = λ i → supportedFinite (h (decode finiteA i))

    go : ∀ {tree′ word} → RelatedFinite tree′ word →
      RelatedFinite
        (paraGo
          (paraAlgebra {G = WordF k} {T = Word k} {U = vec (Word k) n}
            (flatWordF k) (eval (supported-wordParaHandlerᴾ sg sh)) values)
          tree′ (λ ()))
        (Source.eval (Source.Pr g h) (word ∷ xs))
    go related-[] = correctFinite g parameters
    go (related-∷ {a = a} {child = childValue} {xs = childWord} child) =
      Eq.subst
        (λ target → RelatedFinite target
          (Source.eval (Source.Pr g h) ((a ∷ᴸ childWord) ∷ xs)))
        (Eq.sym
          (Eq.trans
            (para-letterᴾ sg sh (encode finiteA a) childValue values)
            (Eq.cong
              (λ b → eval (supportedFinite (h b))
                (paraFlat {G = WordF k} {T = Word k}
                   {U = vec (Word k) n} (flatWordF k)
                   (eval (supported-wordParaHandlerᴾ sg sh))
                   (childValue , values) ,
                 childValue , values))
              (decode-encode finiteA a))))
        (correctFinite (h a)
          (related-v∷ (go child) (related-v∷ child parameters)))

  correctFinite* [] related = related-v[]
  correctFinite* (p ∷ ps) related =
    related-v∷ (correctFinite p related) (correctFinite* ps related)
