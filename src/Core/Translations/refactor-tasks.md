# Later tasks: generic P/F interdefinability refactor

The first-order and higher-order P/F interdefinability proofs are currently
separate, intentionally mechanical developments.  This file tracks the
medium-term cleanup that should replace the duplication once both versions are
stable.

## Goal

Factor the common proof that paramorphism-primitive and fold-primitive
presentations are equivalent.  The proof should be parameterized by the
categorical and inductive-type structure it actually uses, with exponentials
treated as an optional extension rather than baked into the argument.

## Proposed steps

1. Define a small record for the shared syntax surface:
   category operations, terminal/initial objects, products, sums, functorial
   action, strength, `con`, and either primitive `P` or primitive `F`.
2. Define a corresponding record of equations:
   congruence, category/product/sum laws, functoriality, strength naturality,
   `strength-π₁`, and the primitive recursion or fold computation/uniqueness
   laws.
3. Move the common derived lemmas from
   `Core.Translations.PRFOParamorphismFold` and
   `Core.Translations.PRHOParamorphismFold` into one parameterized module:
   derived `F` from `P`, derived `P` from `F`, β-laws, uniqueness laws, equation
   preservation, and round-trip proofs.
4. Instantiate the generic module for FO.
5. Instantiate the generic module for HO, adding only the structural
   exponential cases (`lam`, `apply`, `⇒-β`, `⇒-η`) outside the generic core.
6. Decide whether the generic layer should also expose derived distributivity
   facts or leave them in the HO/FO-specific equation modules.
7. After the refactor, delete or shrink the duplicated proof bodies in the FO
   and HO translation modules to thin instantiation wrappers.

## Open design questions

- Investigate whether the current restriction
  ``_`⇒_ : Ty HO 0 → Ty HO n → Ty HO n`` can be relaxed by treating
  higher-order type codes as bifunctors, with one index for contravariant
  positions and one for covariant positions.  This could allow function
  domains to mention type variables while preserving a principled functorial
  action, but it would likely require replacing the present unary `fmap` and
  `strength` interface with a bifunctorial action and rechecking the P/F
  equivalence proofs against that more general structure.

## Guardrails

- Keep the current first-order and higher-order modules typechecking during the
  refactor.
- Do not abstract over more than the P/F proof needs.  In particular,
  exponentials are not part of the core P/F argument.
- Preserve the names of the public theorems (`toP-preserves`, `toF-preserves`,
  `toP-toF`, `toF-toP`) or re-export them under the existing names.
