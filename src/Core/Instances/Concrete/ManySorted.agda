{-# OPTIONS --safe #-}

module Core.Instances.Concrete.ManySorted where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map)
open import Relation.Binary.PropositionalEquality using (sym; subst)

open import Core.PRFO
open import Core.Semantics.Inductive using (paraGo)
open import Core.Instances.Common
open import Core.Instances.ManySorted
import Core.Instances.Source.ManySorted as Source
open import Core.Instances.Concrete.Evaluator
open import Core.Instances.Concrete.Supported
open import Core.Instances.Concrete.Casts using (mapSem)
import Core.Instances.Concrete.Trees as Trees

supported : ∀ {S n s} {Sig : Source.Signature S} {ss : Vec S n}
  (p : Source.PR Sig (ss , s)) → Supported (compile p)
supported* : ∀ {S n m} {Sig : Source.Signature S}
  {ss : Vec S n} {us : Vec S m} (ps : Source.PR* Sig (ss , us)) →
  Supported (compile* ps)

supported-steps : ∀ {S n} {Sig : Source.Signature S}
  {ss : Vec S n} (res : S → S)
  (steps : (a : Fin (Source.count Sig)) →
    Source.PR Sig
      ((map res (Source.inputs Sig a) ++ Source.inputs Sig a) ++ ss ,
       res (Source.output Sig a)))
  (a : Fin (Source.count Sig)) → Supported (compile (steps a))
supported-steps res steps a = supported (steps a)

supported {Sig = Sig} (Source.σ a) = supported-con (Source.ranks Sig) a
supported (Source.π i) = supported-lookup i
supported (Source.C f fs) = s-C (supported f) (supported* fs)
supported {Sig = Sig} (Source.P res steps) =
  s-P (Branches (Source.ranks Sig)) (flatBranches (Source.ranks Sig))
    (supported-paraHandler (Source.ranks Sig) (supported-steps res steps))

supported* Source.[] = s-⊤
supported* (p Source.∷ ps) = s-# (supported p) (supported* ps)

mutual
  data Related {S : Set} {Sig : Source.Signature S} : ∀ {s : S} →
    Sem (Target Sig) → Source.Term Sig s → Set where
    related-con : ∀ {a children values} →
      RelatedEnv (Source.inputs Sig a) values (Source.tabulateEnv children) →
      Related (eval (supported-con (Source.ranks Sig) a) values)
              (Source.con a children)

  data RelatedEnv {S : Set} {Sig : Source.Signature S} :
    ∀ {n} (ss : Vec S n) →
    Sem (vec (Target Sig) n) → Source.Env Sig ss → Set where
    related-[] : RelatedEnv [] tt Source.[]
    related-∷ : ∀ {n s} {ss : Vec S n} {x xs y ys} →
      Related {Sig = Sig} {s = s} x y → RelatedEnv ss xs ys →
      RelatedEnv (s ∷ ss) (x , xs) (y Source.∷ ys)

lookup-related : ∀ {S n} {Sig : Source.Signature S} {ss : Vec S n}
  (i : Fin n) {values : Sem (vec (Target Sig) n)} {env : Source.Env Sig ss} →
  RelatedEnv ss values env →
  Related (eval (supported-lookup i) values) (Source.lookupEnv env i)
lookup-related zero (related-∷ x xs) = x
lookup-related (suc i) (related-∷ x xs) = lookup-related i xs

append-related : ∀ {S m n} {Sig : Source.Signature S}
  {ss : Vec S m} {us : Vec S n}
  {xs : Sem (vec (Target Sig) m)} {ys : Sem (vec (Target Sig) n)}
  {source-xs : Source.Env Sig ss} {source-ys : Source.Env Sig us} →
  RelatedEnv ss xs source-xs → RelatedEnv us ys source-ys →
  RelatedEnv (ss ++ us)
    (eval (supported-appendVec m n) (xs , ys))
    (Source.appendEnv source-xs source-ys)
append-related related-[] ys = ys
append-related (related-∷ x xs) ys =
  related-∷ x (append-related xs ys)

prepare-related : ∀ {S r n} {Sig : Source.Signature S}
  {res : S → S} {input-sorts : Vec S r} {parameter-sorts : Vec S n}
  {results children : Sem (vec (Target Sig) r)}
  {parameters : Sem (vec (Target Sig) n)}
  {source-results : Source.Env Sig (map res input-sorts)}
  {source-children : Source.Env Sig input-sorts}
  {source-parameters : Source.Env Sig parameter-sorts} →
  RelatedEnv (map res input-sorts) results source-results →
  RelatedEnv input-sorts children source-children →
  RelatedEnv parameter-sorts parameters source-parameters →
  RelatedEnv ((map res input-sorts ++ input-sorts) ++ parameter-sorts)
    (eval (supported-preparePara r n)
      (Trees.zipSem r results children , parameters))
    (Source.appendEnv (Source.appendEnv source-results source-children)
      source-parameters)
prepare-related {r = r} {results = results} {children = children}
  result-rel child-rel parameter-rel
  rewrite Trees.splitPairs-zip r results children =
  append-related (append-related result-rel child-rel) parameter-rel

correct : ∀ {S n s} {Sig : Source.Signature S} {ss : Vec S n}
  (p : Source.PR Sig (ss , s))
  {values : Sem (vec (Target Sig) n)} {env : Source.Env Sig ss} →
  RelatedEnv ss values env →
  Related (eval (supported p) values) (Source.eval p env)
correct* : ∀ {S n m} {Sig : Source.Signature S}
  {ss : Vec S n} {us : Vec S m} (ps : Source.PR* Sig (ss , us))
  {values : Sem (vec (Target Sig) n)} {env : Source.Env Sig ss} →
  RelatedEnv ss values env →
  RelatedEnv us (eval (supported* ps) values) (Source.eval* ps env)

correct {Sig = Sig} (Source.σ a) related =
  related-con (tabulate-related related)
  where
  tabulate-related : ∀ {n} {ss : Vec _ n}
    {values : Sem (vec (Target Sig) n)} {env : Source.Env Sig ss} →
    RelatedEnv ss values env →
    RelatedEnv ss values (Source.tabulateEnv (Source.lookupEnv env))
  tabulate-related related-[] = related-[]
  tabulate-related (related-∷ x xs) =
    related-∷ x (tabulate-related xs)
correct (Source.π i) related = lookup-related i related
correct (Source.C f fs) related = correct f (correct* fs related)
correct {n = suc n} {Sig = Sig} (Source.P res steps)
  {values = tree , values} {env = term Source.∷ terms}
  (related-∷ first parameters) = go first
  where
  handler : Supported
    (paraHandler (Source.ranks Sig) (λ a → compile (steps a)))
  handler = supported-paraHandler (Source.ranks Sig) (supported-steps res steps)

  go : ∀ {s} {tree′ : Sem (Target Sig)} {term′ : Source.Term Sig s} →
    Related tree′ term′ →
    Related
      (paraGo
        (paraAlgebra {G = Branches (Source.ranks Sig)} {T = Target Sig}
          {U = vec (Target Sig) n} (flatBranches (Source.ranks Sig))
          (eval handler) values)
        tree′ (λ ()))
      (Source.eval (Source.P res steps) (term′ Source.∷ terms))
  go (related-con {a = a} {children = source-children}
      {values = child-values} child-rel) =
    subst
      (λ target → Related target
        (Source.eval (Source.P res steps)
          (Source.con a source-children Source.∷ terms)))
      (sym (Trees.para-con (Source.ranks Sig)
        (λ i → compile (steps i)) (supported-steps res steps)
        a child-values values))
      (subst
        (λ source → Related
          (eval (supported (steps a))
            (eval (supported-preparePara (lookup (Source.ranks Sig) a) n)
              (Trees.zipSem (lookup (Source.ranks Sig) a)
                (mapSem {T = Target Sig} {U = Target Sig} recur
                  (lookup (Source.ranks Sig) a) child-values)
                child-values , values)))
          source)
        (sym (Source.eval-P-con res steps a source-children terms))
        (correct (steps a)
          (prepare-related
            (recurse (Source.inputs Sig a) source-children child-rel)
            child-rel parameters)))
    where
    recur : Sem (Target Sig) → Sem (Target Sig)
    recur child =
      paraGo
        (paraAlgebra {G = Branches (Source.ranks Sig)} {T = Target Sig}
          {U = vec (Target Sig) n} (flatBranches (Source.ranks Sig))
          (eval handler) values)
        child (λ ())

    source-recur : ∀ {s} → Source.Term Sig s → Source.Term Sig (res s)
    source-recur child =
      Source.eval (Source.P res steps) (child Source.∷ terms)

    recurse : ∀ {r} (input-sorts : Vec _ r)
      (source-children : (i : Fin r) →
        Source.Term Sig (lookup input-sorts i))
      {children : Sem (vec (Target Sig) r)} →
      RelatedEnv input-sorts children (Source.tabulateEnv source-children) →
      RelatedEnv (map res input-sorts)
        (mapSem {T = Target Sig} {U = Target Sig} recur r children)
        (Source.tabulateMapEnv res input-sorts
          (λ i → source-recur (source-children i)))
    recurse [] source-children related-[] = related-[]
    recurse (s ∷ input-sorts) source-children (related-∷ child children) =
      related-∷ (go child)
        (recurse input-sorts (λ i → source-children (suc i)) children)

correct* Source.[] related = related-[]
correct* (p Source.∷ ps) related =
  related-∷ (correct p related) (correct* ps related)
