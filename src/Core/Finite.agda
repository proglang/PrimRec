{-# OPTIONS --safe #-}

module Core.Finite where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

record Finite (A : Set) : Set where
  constructor finite
  field
    size          : ℕ
    encode        : A → Fin size
    decode        : Fin size → A
    decode-encode : (a : A) → decode (encode a) ≡ a
    encode-decode : (i : Fin size) → encode (decode i) ≡ i

open Finite public

finiteFin : (n : ℕ) → Finite (Fin n)
finiteFin n = finite n (λ i → i) (λ i → i) (λ i → refl) (λ i → refl)
