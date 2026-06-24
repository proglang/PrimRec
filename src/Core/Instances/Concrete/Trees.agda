{-# OPTIONS --safe #-}

module Core.Instances.Concrete.Trees where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_; _++_; lookup; map; tabulate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym; subst)

open import Core.PRFO
open import Core.Semantics.Inductive using (paraGo)
open import Core.Instances.Common
open import Core.Instances.Trees
import Core.Instances.Source.Trees as Source
open import Core.Instances.Concrete.Evaluator
open import Core.Instances.Concrete.Supported
open import Core.Instances.Concrete.Casts

supported : ∀ {R n} (p : Source.PR R n) → Supported (compile p)
supported* : ∀ {R m n} (ps : Vec (Source.PR R n) m) → Supported (compile* ps)

supported-steps : ∀ {R n}
  (steps : (a : Fin (Source.count R)) →
    Source.PR R ((Source.rank R a + Source.rank R a) + n))
  (a : Fin (Source.count R)) → Supported (compile (steps a))
supported-steps steps a = supported (steps a)

supported {R} (Source.σ a) = supported-con (Source.ranks R) a
supported (Source.π i) = supported-lookup i
supported (Source.C f fs) = s-C (supported f) (supported* fs)
supported {R} (Source.P steps) =
  s-P (Branches (Source.ranks R)) (flatBranches (Source.ranks R))
    (supported-paraHandler (Source.ranks R) (supported-steps steps))

supported* [] = s-⊤
supported* (p ∷ ps) = s-# (supported p) (supported* ps)

zipSem : ∀ {T U} (n : ℕ) → Sem (vec T n) → Sem (vec U n) →
         Sem (vec (T `× U) n)
zipSem zero tt tt = tt
zipSem (suc n) (x , xs) (y , ys) = (x , y) , zipSem n xs ys

mapSem-pair : ∀ {T U} (f : Sem T → Sem U) (n : ℕ)
  (xs : Sem (vec T n)) →
  mapSem {T = T} {U = U `× T} (λ x → f x , x) n xs ≡
  zipSem {T = U} {U = T} n (mapSem {T = T} {U = U} f n xs) xs
mapSem-pair f zero tt = refl
mapSem-pair {T = T} {U = U} f (suc n) (x , xs)
  rewrite mapSem-pair {T = T} {U = U} f n xs = refl

splitPairs-zip : ∀ {T U} (n : ℕ) (xs : Sem (vec T n)) (ys : Sem (vec U n)) →
  eval (supported-splitPairs n) (zipSem n xs ys) ≡ (xs , ys)
splitPairs-zip zero tt tt = refl
splitPairs-zip (suc n) (x , xs) (y , ys)
  rewrite splitPairs-zip n xs ys = refl

map-proj₁-tabulate : ∀ {A B : Set} {n} (pairs : Fin n → A × B) →
  map proj₁ (tabulate pairs) ≡ tabulate (λ i → proj₁ (pairs i))
map-proj₁-tabulate {n = zero} pairs = refl
map-proj₁-tabulate {n = suc n} pairs =
  cong₂ _∷_ refl (map-proj₁-tabulate (λ i → pairs (suc i)))

map-proj₂-tabulate : ∀ {A B : Set} {n} (pairs : Fin n → A × B) →
  map proj₂ (tabulate pairs) ≡ tabulate (λ i → proj₂ (pairs i))
map-proj₂-tabulate {n = zero} pairs = refl
map-proj₂-tabulate {n = suc n} pairs =
  cong₂ _∷_ refl (map-proj₂-tabulate (λ i → pairs (suc i)))

para-con : ∀ {k n} (rs : Vec ℕ k)
  (steps : (i : Fin k) →
    vec (Tree rs) ((lookup rs i + lookup rs i) + n) →ᴾ Tree rs)
  (ss : (i : Fin k) → Supported (steps i))
  (i : Fin k) (children : Sem (vec (Tree rs) (lookup rs i)))
  (parameters : Sem (vec (Tree rs) n)) →
  paraGo
    (paraAlgebra {G = Branches rs} {T = Tree rs} {U = vec (Tree rs) n}
      (flatBranches rs)
      (eval (supported-paraHandler rs ss)) parameters)
    (eval (supported-con rs i) children) (λ ())
  ≡
  eval (ss i)
    (eval (supported-preparePara (lookup rs i) n)
      (zipSem {T = Tree rs} {U = Tree rs} (lookup rs i)
        (mapSem {T = Tree rs} {U = Tree rs}
          (λ child →
            paraGo
              (paraAlgebra {G = Branches rs} {T = Tree rs} {U = vec (Tree rs) n}
                (flatBranches rs)
                (eval (supported-paraHandler rs ss)) parameters)
              child (λ ()))
          (lookup rs i) children)
        children , parameters))
para-con {k = k} {n = n} rs steps ss i children parameters =
  trans
    (para-foldFlat-β {G = Branches rs} {T = Tree rs}
      {U = vec (Tree rs) n} (flatBranches rs)
      handlerSem
      (eval (supported-injectBranch {T = Tree rs} rs i) children) parameters)
    (trans
      (cong handlerSem
        (cong (λ (layer : Sem (Branches rs ⇐ (Tree rs `× Tree rs))) →
                layer , parameters)
          (trans
            (paraStep-as-fmap {G = Branches rs} {T = Tree rs}
              {U = vec (Tree rs) n} (flatBranches rs)
              handlerSem parameters
              (eval (supported-injectBranch {T = Tree rs} rs i) children))
            (trans
              (fmap-injectBranch {T = Tree rs} {U = Tree rs `× Tree rs}
                rs i step children)
              (cong (eval (supported-injectBranch
                {T = Tree rs `× Tree rs} rs i))
                (mapSem-pair {T = Tree rs} {U = Tree rs}
                  recur (lookup rs i) children))))))
      (case-inject rs handlers supported-handlers i pairs parameters))
  where
  handlers : (j : Fin k) →
    vec (Tree rs `× Tree rs) (lookup rs j) `× vec (Tree rs) n →ᴾ Tree rs
  handlers j = C (steps j) (preparePara (lookup rs j) n)

  supported-handlers : (j : Fin k) → Supported (handlers j)
  supported-handlers j = s-C (ss j) (supported-preparePara (lookup rs j) n)

  handlerSem :
    Sem ((Branches rs ⇐ (Tree rs `× Tree rs)) `× vec (Tree rs) n) →
    Sem (Tree rs)
  handlerSem = eval (supported-paraHandler rs ss)

  recur : Sem (Tree rs) → Sem (Tree rs)
  recur child =
    paraFlat {G = Branches rs} {T = Tree rs} {U = vec (Tree rs) n}
      (flatBranches rs) handlerSem (child , parameters)

  step : Sem (Tree rs) → Sem (Tree rs `× Tree rs)
  step child = recur child , child

  pairs : Sem (vec (Tree rs `× Tree rs) (lookup rs i))
  pairs = zipSem {T = Tree rs} {U = Tree rs} (lookup rs i)
    (mapSem {T = Tree rs} {U = Tree rs} recur (lookup rs i) children)
    children

mutual
  data Related {R : Source.Ranked} : Sem (Target R) → Source.Term R → Set where
    related-con : ∀ {a children values} →
      Related* (Source.rank R a) values (tabulate children) →
      Related (eval (supported-con (Source.ranks R) a) values)
              (Source.con a children)

  data Related* {R : Source.Ranked} :
    (n : ℕ) → Sem (vec (Target R) n) → Vec (Source.Term R) n → Set where
    related-[] : Related* zero tt []
    related-∷ : ∀ {k x xs y ys} → Related x y → Related* k xs ys →
      Related* (suc k) (x , xs) (y ∷ ys)

lookup-related : ∀ {R n} (i : Fin n) {values : Sem (vec (Target R) n)}
  {terms : Vec (Source.Term R) n} → Related* n values terms →
  Related (eval (supported-lookup i) values) (lookup terms i)
lookup-related zero (related-∷ rx rxs) = rx
lookup-related (suc i) (related-∷ rx rxs) = lookup-related i rxs

append-related : ∀ {R m n}
  {xs : Sem (vec (Target R) m)} {ys : Sem (vec (Target R) n)}
  {us : Vec (Source.Term R) m} {vs : Vec (Source.Term R) n} →
  Related* m xs us → Related* n ys vs →
  Related* (m + n) (eval (supported-appendVec m n) (xs , ys)) (us ++ vs)
append-related related-[] ys = ys
append-related (related-∷ x xs) ys = related-∷ x (append-related xs ys)

prepare-related : ∀ {R r n}
  {results children : Sem (vec (Target R) r)}
  {parameters : Sem (vec (Target R) n)}
  {rs cs : Vec (Source.Term R) r} {ps : Vec (Source.Term R) n} →
  Related* r results rs → Related* r children cs → Related* n parameters ps →
  Related* ((r + r) + n)
    (eval (supported-preparePara r n) (zipSem r results children , parameters))
    ((rs ++ cs) ++ ps)
prepare-related result-rel child-rel parameter-rel =
  prepare result-rel child-rel parameter-rel
  where
  prepare : ∀ {R r n}
    {results children : Sem (vec (Target R) r)}
    {parameters : Sem (vec (Target R) n)}
    {rs cs : Vec (Source.Term R) r} {ps : Vec (Source.Term R) n} →
    Related* r results rs → Related* r children cs → Related* n parameters ps →
    Related* ((r + r) + n)
      (eval (supported-preparePara r n) (zipSem r results children , parameters))
      ((rs ++ cs) ++ ps)
  prepare {r = r} {results = results} {children = children} result-rel child-rel parameter-rel
    rewrite splitPairs-zip r results children =
      append-related (append-related result-rel child-rel) parameter-rel

correct : ∀ {R n} (p : Source.PR R n)
  {values : Sem (vec (Target R) n)} {terms : Vec (Source.Term R) n} →
  Related* n values terms →
  Related (eval (supported p) values) (Source.eval p terms)
correct* : ∀ {R m n} (ps : Vec (Source.PR R n) m)
  {values : Sem (vec (Target R) n)} {terms : Vec (Source.Term R) n} →
  Related* n values terms →
  Related* m (eval (supported* ps) values) (Source.eval* ps terms)

correct {R} (Source.σ a) related =
  related-con (tabulate-related related)
  where
  tabulate-related : ∀ {n} {values : Sem (vec (Target R) n)}
    {terms : Vec (Source.Term R) n} → Related* n values terms →
    Related* n values (tabulate (lookup terms))
  tabulate-related related-[] = related-[]
  tabulate-related (related-∷ x xs) = related-∷ x (tabulate-related xs)
correct (Source.π i) related = lookup-related i related
correct (Source.C f fs) related = correct f (correct* fs related)
correct {R} {suc n} (Source.P steps) {values = tree , values}
  {terms = term ∷ terms} (related-∷ first parameters) = go first
  where
  handler : Supported (paraHandler (Source.ranks R) (λ a → compile (steps a)))
  handler = supported-paraHandler (Source.ranks R) (supported-steps steps)

  go : ∀ {tree′ term′} → Related tree′ term′ →
    Related
      (paraGo
        (paraAlgebra {G = Branches (Source.ranks R)} {T = Target R}
          {U = vec (Target R) n} (flatBranches (Source.ranks R))
          (eval handler) values)
        tree′ (λ ()))
      (Source.eval (Source.P steps) (term′ ∷ terms))
  go (related-con {a = a} {children = source-children}
      {values = child-values} child-rel) =
    subst
      (λ target → Related target
        (Source.eval (Source.P steps) (Source.con a source-children ∷ terms)))
      (sym (para-con (Source.ranks R)
        (λ i → compile (steps i)) (supported-steps steps)
        a child-values values))
      (correct (steps a)
        (subst
          (Related* ((Source.rank R a + Source.rank R a) + n)
            (eval (supported-preparePara (Source.rank R a) n)
              (zipSem (Source.rank R a)
                (mapSem
                  (λ child →
                    paraGo
                      (paraAlgebra {G = Branches (Source.ranks R)}
                        {T = Target R} {U = vec (Target R) n}
                        (flatBranches (Source.ranks R))
                        (eval handler) values)
                      child (λ ()))
                  (Source.rank R a) child-values)
                child-values , values)))
          (sym source-arguments)
          (prepare-related
            (recurse (Source.rank R a) source-children child-rel)
            child-rel parameters)))
    where
    recur : Sem (Target R) → Sem (Target R)
    recur child =
      paraGo
        (paraAlgebra {G = Branches (Source.ranks R)} {T = Target R}
          {U = vec (Target R) n} (flatBranches (Source.ranks R))
          (eval handler) values)
        child (λ ())

    source-recur : Source.Term R → Source.Term R
    source-recur child = Source.eval (Source.P steps) (child ∷ terms)

    recurse : ∀ (k : ℕ) (source-children : Fin k → Source.Term R)
      {children : Sem (vec (Target R) k)} →
      Related* k children (tabulate source-children) →
      Related* k
        (mapSem recur k children)
        (tabulate (λ i → source-recur (source-children i)))
    recurse zero source-children related-[] = related-[]
    recurse (suc k) source-children (related-∷ child children) =
      related-∷ (go child) (recurse k (λ i → source-children (suc i)) children)

    pair-children : Fin (Source.rank R a) → Source.Term R × Source.Term R
    pair-children i = source-recur (source-children i) , source-children i

    source-arguments :
      ((map proj₁ (tabulate pair-children) ++
        map proj₂ (tabulate pair-children)) ++ terms) ≡
      ((tabulate (λ i → source-recur (source-children i)) ++
        tabulate source-children) ++ terms)
    source-arguments =
      cong₂ (λ results children → (results ++ children) ++ terms)
        (map-proj₁-tabulate pair-children)
        (map-proj₂-tabulate pair-children)

correct* [] related = related-[]
correct* (p ∷ ps) related = related-∷ (correct p related) (correct* ps related)
