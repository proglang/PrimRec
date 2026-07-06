{-# OPTIONS --safe #-}

module Core.Instances.Equations.ManySorted where

open import Data.Fin using (Fin)
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; _∷_; map; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Core.Instances.ManySorted
import Core.Instances.Equations.Target as TargetEq
import Core.Instances.Equations.Trees as TreeEq
import Core.Instances.Source.ManySorted as Source
import Core.Instances.Source.Trees as TreeSource

append* : ∀ {S n m k} {Sig : Source.Signature S}
  {ss : Vec S n} {us : Vec S m} {vs : Vec S k} →
  Source.PR* Sig (ss , us) → Source.PR* Sig (ss , vs) →
  Source.PR* Sig (ss , us ++ vs)
append* Source.[] ys = ys
append* (p Source.∷ ps) ys = p Source.∷ append* ps ys

recursiveResults : ∀ {S n m r} {Sig : Source.Signature S}
  {ss : Vec S n} {us : Vec S m} {input-sorts : Vec S r}
  (res : S → S)
  (steps : (a : Fin (Source.count Sig)) →
    Source.PR Sig
      ((map res (Source.inputs Sig a) ++ Source.inputs Sig a) ++ ss ,
       res (Source.output Sig a))) →
  Source.PR* Sig (us , input-sorts) → Source.PR* Sig (us , ss) →
  Source.PR* Sig (us , map res input-sorts)
recursiveResults res steps Source.[] parameters = Source.[]
recursiveResults res steps (child Source.∷ children) parameters =
  Source.C (Source.Pr res steps) (child Source.∷ parameters) Source.∷
  recursiveResults res steps children parameters

infix 4 _≈ₛ_ _≈ₛ*_

mutual
  data _≈ₛ_ {S : Set} {Sig : Source.Signature S} :
    ∀ {n s} {ss : Vec S n} →
    Source.PR Sig (ss , s) → Source.PR Sig (ss , s) → Set where
    reflₛ : ∀ {n s} {ss : Vec S n} {p : Source.PR Sig (ss , s)} →
      p ≈ₛ p
    symₛ : ∀ {n s} {ss : Vec S n} {p q : Source.PR Sig (ss , s)} →
      p ≈ₛ q → q ≈ₛ p
    transₛ : ∀ {n s} {ss : Vec S n}
      {p q r : Source.PR Sig (ss , s)} →
      p ≈ₛ q → q ≈ₛ r → p ≈ₛ r
    C-congₛ : ∀ {n m s} {ss : Vec S n} {us : Vec S m}
      {f g : Source.PR Sig (us , s)}
      {fs gs : Source.PR* Sig (ss , us)} →
      f ≈ₛ g → fs ≈ₛ* gs → Source.C f fs ≈ₛ Source.C g gs
    Pr-congₛ : ∀ {n s₀} {ss : Vec S n} (res : S → S)
      {hs ks : (a : Fin (Source.count Sig)) →
        Source.PR Sig
          ((map res (Source.inputs Sig a) ++ Source.inputs Sig a) ++ ss ,
           res (Source.output Sig a))} →
      ((a : Fin (Source.count Sig)) → hs a ≈ₛ ks a) →
      Source.Pr {s₀ = s₀} res hs ≈ₛ Source.Pr res ks
    Pr-βₛ : ∀ {n m} {ss : Vec S n} {us : Vec S m}
      (res : S → S)
      (steps : (a : Fin (Source.count Sig)) →
        Source.PR Sig
          ((map res (Source.inputs Sig a) ++ Source.inputs Sig a) ++ ss ,
           res (Source.output Sig a)))
      (a : Fin (Source.count Sig))
      (children : Source.PR* Sig (us , Source.inputs Sig a))
      (parameters : Source.PR* Sig (us , ss)) →
      Source.C (Source.Pr {s₀ = Source.output Sig a} res steps)
        (Source.C (Source.σ a) children Source.∷ parameters) ≈ₛ
      Source.C (steps a)
        (append* (append* (recursiveResults res steps children parameters) children)
          parameters)

  data _≈ₛ*_ {S : Set} {Sig : Source.Signature S} :
    ∀ {n m} {ss : Vec S n} {us : Vec S m} →
    Source.PR* Sig (ss , us) → Source.PR* Sig (ss , us) → Set where
    []ₛ : ∀ {n} {ss : Vec S n} →
      _≈ₛ*_ {Sig = Sig} {ss = ss} Source.[] Source.[]
    _∷ₛ_ : ∀ {n m s} {ss : Vec S n} {us : Vec S m}
      {p q : Source.PR Sig (ss , s)}
      {ps qs : Source.PR* Sig (ss , us)} →
      p ≈ₛ q → ps ≈ₛ* qs →
      (p Source.∷ ps) ≈ₛ* (q Source.∷ qs)

erase-append : ∀ {S n m k} {Sig : Source.Signature S}
  {ss : Vec S n} {us : Vec S m} {vs : Vec S k}
  (xs : Source.PR* Sig (ss , us)) (ys : Source.PR* Sig (ss , vs)) →
  erase* (append* xs ys) ≡ erase* xs ++ erase* ys
erase-append Source.[] ys = refl
erase-append (x Source.∷ xs) ys =
  cong (erase x ∷_) (erase-append xs ys)

erase-results : ∀ {S n m r} {Sig : Source.Signature S}
  {ss : Vec S n} {us : Vec S m} {input-sorts : Vec S r}
  (res : S → S)
  (steps : (a : Fin (Source.count Sig)) →
    Source.PR Sig
      ((map res (Source.inputs Sig a) ++ Source.inputs Sig a) ++ ss ,
       res (Source.output Sig a)))
  (children : Source.PR* Sig (us , input-sorts))
  (parameters : Source.PR* Sig (us , ss)) →
  erase* (recursiveResults res steps children parameters) ≡
  map
    (λ child →
      TreeSource.C (TreeSource.Pr (λ a → erase (steps a)))
        (child ∷ erase* parameters))
    (erase* children)
erase-results res steps Source.[] parameters = refl
erase-results res steps (child Source.∷ children) parameters =
  cong (_ ∷_) (erase-results res steps children parameters)

erase-preserves : ∀ {S n s} {Sig : Source.Signature S} {ss : Vec S n}
  {p q : Source.PR Sig (ss , s)} →
  p ≈ₛ q → erase p TreeEq.≈ₛ erase q
erase-preserves* : ∀ {S n m} {Sig : Source.Signature S}
  {ss : Vec S n} {us : Vec S m}
  {ps qs : Source.PR* Sig (ss , us)} →
  ps ≈ₛ* qs → erase* ps TreeEq.≈ₛ* erase* qs

erase-preserves reflₛ = TreeEq.reflₛ
erase-preserves (symₛ equation) = TreeEq.symₛ (erase-preserves equation)
erase-preserves (transₛ first second) =
  TreeEq.transₛ (erase-preserves first) (erase-preserves second)
erase-preserves (C-congₛ f fs) =
  TreeEq.C-congₛ (erase-preserves f) (erase-preserves* fs)
erase-preserves (Pr-congₛ res pointwise) =
  TreeEq.Pr-congₛ (λ a → erase-preserves (pointwise a))
erase-preserves (Pr-βₛ res steps a children parameters)
  rewrite erase-append
            (append* (recursiveResults res steps children parameters) children)
            parameters
        | erase-append (recursiveResults res steps children parameters) children
        | erase-results res steps children parameters =
  TreeEq.Pr-βₛ (λ i → erase (steps i)) a (erase* children) (erase* parameters)

erase-preserves* []ₛ = TreeEq.[]ₛ
erase-preserves* (p ∷ₛ ps) =
  erase-preserves p TreeEq.∷ₛ erase-preserves* ps

preserves : ∀ {S n s} {Sig : Source.Signature S} {ss : Vec S n}
  {p q : Source.PR Sig (ss , s)} →
  p ≈ₛ q → compile p TargetEq.≈ᴵ compile q
preserves equation = TreeEq.preserves (erase-preserves equation)

preserves* : ∀ {S n m} {Sig : Source.Signature S}
  {ss : Vec S n} {us : Vec S m}
  {ps qs : Source.PR* Sig (ss , us)} →
  ps ≈ₛ* qs → compile* ps TargetEq.≈ᴵ compile* qs
preserves* equation = TreeEq.preserves* (erase-preserves* equation)
