# PrimRec Agda sources

This directory formalizes several presentations of primitive recursion over naturals, words, ranked trees, heterogeneous trees, categorical combinators, and fragments of System T. Files ending in `.lagda` are literate Agda sources that may also contain LaTeX markup; files ending in `.agda` are ordinary Agda modules.

## File guide

### [`EvalPrConstructor.lagda`](EvalPrConstructor.lagda)

Defines the generic primitive-recursion operator `para` and specializes it to vector-argument natural-number functions. It proves equivalence with the `PR-Nat` primitive-recursion constructor and develops an alternative bounded-iteration implementation.

### [`FinProperties.agda`](FinProperties.agda)

Collects arithmetic laws for weakening and raising `Fin` indices. These lemmas describe how injections compose with addition and successor and are used by context-manipulation proofs elsewhere.

### [`HList.agda`](HList.agda)

Defines heterogeneous lists indexed by a list of sorts. It supplies typed lookup, append, and map operations for values whose type depends on the corresponding sort.

### [`HTreesVec.agda`](HTreesVec.agda)

Defines vector-valued primitive-recursive programs over many-sorted ranked algebras. It also defines indexed algebra values and evaluates zero-output, pairing, constructors, projections, composition, and structural recursion.

### [`HVec.agda`](HVec.agda)

Defines heterogeneous vectors indexed by a vector of sorts, together with typed lookup, append, map, and conversion operations. It also provides reverse-accumulating append and supporting equality lemmas used by the System T developments.

### [`NatsToWords.lagda`](NatsToWords.lagda)

Embeds primitive recursion over naturals into primitive recursion over words on the unit alphabet and proves semantic soundness. It also gives the reverse translation and its soundness proof, identifying unit words with unary naturals.

### [`NatsVec-CC.lagda`](NatsVec-CC.lagda)

Translates vector-valued natural primitive recursion into the product-based categorical calculus from `PR-CC`. It defines tuple encodings, structural isomorphisms, projections, and a soundness theorem for the translation.

### [`NatsVecToNats.lagda`](NatsVecToNats.lagda)

Compiles vector-valued natural primitive recursion into vectors of ordinary scalar primitive-recursive programs. Simultaneous recursion is implemented by nested pairing, and the file proves encoding, decoding, step, and overall semantic soundness.

### [`PR-CC-Ctx-ind-alt.agda`](PR-CC-Ctx-ind-alt.agda)

Presents a contextual, lambda-based language over the alternative polynomial inductive-type calculus from `PR-CC-ind-alt`. It develops weakening and point-free-to-contextual soundness, then embeds System T values and expressions with semantic preservation results.

### [`PR-CC-Ctx.agda`](PR-CC-Ctx.agda)

Defines a contextual lambda calculus with sums, products, function types, and inductive types corresponding to the point-free language in `PR-CC-ind`. It implements renaming, substitution, weakening, evaluation, and a sound embedding from the point-free calculus, with some exploratory reverse-translation code left commented.

### [`PR-CC-ind-alt.lagda`](PR-CC-ind-alt.lagda)

Provides an alternative categorical primitive-recursion calculus in which polynomial type operators are separated from closed types. It interprets inductive fixed points using catamorphisms and functor maps and includes translations of natural, word, and tree recursion.

### [`PR-CC-ind-multi.lagda`](PR-CC-ind-multi.lagda)

Explores a version of the inductive categorical calculus with a richer, potentially nested or multiple-inductive type syntax. The core renaming, substitution, arrow syntax, and evaluator are present, while much of the proposed recursion and source-language translation remains commented experimental material.

### [`PR-CC-ind.lagda`](PR-CC-ind.lagda)

Defines the main point-free categorical calculus with sums, products, polynomial inductive types, catamorphisms, and primitive recursion. It develops a substantial renaming/substitution metatheory, semantic interpretation, categorical structural maps, and embeddings of natural, word, and ranked-tree primitive recursion.

### [`PR-CC.lagda`](PR-CC.lagda)

Defines a small categorical language of natural numbers, unit, products, composition, and primitive recursion. Its evaluator gives a direct set-theoretic interpretation and serves as the target of the vector-valued natural translation.

### [`PR-CCC-ind.lagda`](PR-CCC-ind.lagda)

Extends the inductive categorical calculus to a cartesian closed setting by adding exponential types, application, and lambda abstraction. It proves structural and exponential laws, defines distributivity isomorphisms, and embeds natural, word, and ranked-tree primitive recursion.

### [`PR-CCC-properties.lagda`](PR-CCC-properties.lagda)

Translates types and arrows from `PR-CC-ind` into `PR-CCC-ind` and proves compatibility with renaming and substitution. It develops semantic type isomorphisms and arrow preservation, while isolating the remaining difficult functorial and recursion cases as explicit postulates.

### [`PR-Functional.lagda`](PR-Functional.lagda)

Defines a typed, point-free calculus of primitive-recursive functionals using the `S` and `K` combinators, application, recursion, and catamorphism. Typed bracket abstraction compiles first-order projections, composition, primitive-recursion steps, and catamorphism steps from `PR-Nat` into this functional calculus.

### [`PR-HTrees.lagda`](PR-HTrees.lagda)

Defines primitive recursion over heterogeneous trees for a many-sorted ranked signature. It includes indexed vectors of terms and programs, typed structural operations, the evaluator, and an alternative interleaved formulation of the recursion arguments.

### [`PR-Nat-Example.lagda`](PR-Nat-Example.lagda)

Builds standard primitive-recursive arithmetic programs for addition, multiplication, exponentiation, predecessor, subtraction, factorial, comparison, and remainder, proving each implementation correct. It also develops a Cantor-style pairing function, primitive-recursive unpairing programs, and the associated inverse laws.

### [`PR-Nat.lagda`](PR-Nat.lagda)

Defines the core first-order primitive-recursive language over natural numbers and its vector-based evaluator. It includes primitive recursion, catamorphism, the reduction of catamorphism to primitive recursion, projection utilities, and their soundness lemmas.

### [`PR-NatsVec.lagda`](PR-NatsVec.lagda)

Defines vector-valued primitive-recursive functions `PR m n`, representing functions from `ℕᵐ` to `ℕⁿ`. Its evaluator covers empty output, constants, successor, projections, composition, concatenation, and simultaneous primitive recursion.

### [`PR-SystemT0-Embedding.lagda`](PR-SystemT0-Embedding.lagda)

Compiles `PR-Nat` programs into the arity-indexed System T fragment from `System-T0`. It implements composition and primitive recursion using the target combinators and proves the translation semantically sound without function extensionality.

### [`PR-Trees-Examples.lagda`](PR-Trees-Examples.lagda)

Provides small ranked signatures and example terms for binary trees, words represented as trees, and naturals represented as trees. The examples illustrate how `PR-Trees` encodes symbol arities and well-ranked constructor applications.

### [`PR-Trees.lagda`](PR-Trees.lagda)

Defines ranked signatures, well-ranked tree terms, primitive-recursive tree programs, and their evaluator. It also retains an obsolete presentation and an alternative recursion constructor that interleaves recursive results with child terms.

### [`PR-Words.lagda`](PR-Words.lagda)

Defines primitive-recursive programs over lists from an arbitrary alphabet. The evaluator supports empty words, prefixing, projections, composition, and structural recursion over the leading word argument.

### [`PRHVec.agda`](PRHVec.agda)

Defines a heterogeneous-vector-indexed primitive-recursive language whose input and output types are System T types. It supplies scalar and vector evaluation and proves that vector evaluation agrees with heterogeneous mapping of scalar evaluation.

### [`PrimRecWord.lagda`](PrimRecWord.lagda)

Collects several translations among scalar naturals, vector-valued naturals, words, ranked trees, and heterogeneous trees. Its main completed result embeds ranked-tree primitive recursion into a many-sorted heterogeneous-tree calculus and proves soundness, including the transport-heavy recursion case.

### [`System-T-PR-HVec-Embedding.agda`](System-T-PR-HVec-Embedding.agda)

Develops context and projection lemmas intended for compiling the typed `System-T` syntax into `PRHVec`. The final embedding function is still postulated, so this module currently records an interface and supporting infrastructure rather than a completed translation.

### [`System-T.agda`](System-T.agda)

Defines a simply typed System T with natural numbers, function types, heterogeneous environments, application, lambda abstraction, and primitive recursion. It also constructs and verifies closed constant and projection terms, including the heterogeneous reverse-lookup lemmas needed for projections.

### [`System-T0-PR-Embedding.lagda`](System-T0-PR-Embedding.lagda)

Compiles the arity-indexed System T fragment from `System-T0` back into `PR-Nat`. It implements variables, abstraction, application, constants, and primitive recursion and proves the compiler sound using pointwise recursion congruence.

### [`System-T0.lagda`](System-T0.lagda)

Defines an arity-indexed, base-type fragment of System T with variables, lambdas, application, constants, and primitive recursion. It develops weakening, abstraction, composition, projections, and recursion combinators together with evaluation theorems, avoiding any function-extensionality axiom.

### [`T0-SystemT-Embedding.agda`](T0-SystemT-Embedding.agda)

Embeds the arity-indexed `System-T0` language into the fully typed `System-T` language by translating arities to iterated natural function types. It converts environments to heterogeneous vectors and proves evaluation is preserved, using pointwise congruence for primitive recursion.

### [`TreesToHTrees.lagda`](TreesToHTrees.lagda)

Embeds ordinary ranked trees and their primitive-recursive programs into the unit-sorted instance of `PR-HTrees`. It proves that term vectors, lookup, append, program translation, and evaluation are preserved.

### [`Utils.lagda`](Utils.lagda)

Provides shared vector patterns, repeated vectors, and elementary lemmas about repeat, append, and map. It also defines `asType`, a small equality-directed coercion used in dependent constructions.

### [`VecProperties.lagda`](VecProperties.lagda)

Defines reverse-accumulating vector append, fast reversal, and ordinary reversal. It proves lookup laws for raised and opposite `Fin` indices, append associativity and identities, and equivalence of the reversal implementations.

### [`WordsToTrees.lagda`](WordsToTrees.lagda)

Encodes words as unary-branching ranked trees with a distinguished empty-word constructor. It translates word primitive-recursive programs into tree programs and proves semantic soundness for both individual programs and vectors of programs.
