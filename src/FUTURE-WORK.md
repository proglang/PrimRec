# Future Work: Mixed-Variance Higher-Order Type Operators

The current PR-HO type syntax restricts function domains to closed
types:

```agda
_`=>_ : forall {n} -> Ty HO 0 -> Ty HO n -> Ty HO n
```

This is a conservative way to avoid mixed variance.  Exponentials are
not covariant in both arguments: categorically they are bifunctorial as

```text
(- => -) : C^op x C -> C
```

Thus the principled generalization is not merely to allow type variables
in positive positions in function domains.  Instead, higher-order type
codes should be treated as mixed-variance functors, with separate
contravariant and covariant variable contexts:

```text
(C^op)^m x C^n -> C
```

or equivalently as type expressions indexed by negative and positive
variables.  Products and sums preserve variance.  In a function type
`A => B`, variables in `A` have their variance flipped and variables in
`B` keep their variance.  The current closed-domain rule is then the
special case where the negative context of the function domain is empty
by construction.

This bifunctorial formulation subsumes the earlier positive-positions
proposal.  Positivity is still the criterion for forming inductive
types, but it becomes a derived check on the variance of the recursive
variable: `ind G`, `fmap G`, `strength G`, and the recursion principles
are available only when `G` is covariant in that variable overall.  With
this discipline, function domains may mention variables when the whole
type operator remains covariant.  For example, a continuation-like type
`(X => R) => R` is positive in `X` overall: the inner function domain
flips once, and the outer function domain flips again.

This would simplify the conceptual story: PR-HO type operators would no
longer be described as ordinary covariant functors with an ad hoc
closed-domain restriction, but as mixed-variance functors whose positive
fragments support inductive types.  It would not be a small
implementation cleanup.  It would likely require:

- a variance-indexed or two-context `Ty`;
- variance-aware renaming and substitution;
- a mixed-variance action replacing the current unary `fmap`;
- a reformulation of `strength` for the covariant part, or an interface
  that exposes strength only for positive functors;
- recursion, equations, models, and translations parameterized by the
  positive fragment of the mixed-variance syntax;
- rechecking the P/F equivalence proofs against that more general
  interface.

This direction also clarifies the generic P/F refactor.  The generic
proof should abstract over the structure it really needs: a positive
functorial action with strength, a constructor, and either primitive
folds or primitive paramorphisms.  Mixed-variance bifunctors would then
be one richer way to instantiate that interface, not something the core
P/F proof should depend on directly.

# Future Work: Algebraic Interfaces for Syntax and Models

The current raw calculi are inductive datatypes, which is useful for
initial syntax: translations, recursion over programs, and generated
equational theories can pattern match directly on constructors.  A
complementary interface would package the same constructors as records
of operations and laws.  For example, one could define a reusable
signature for PR-FO or PR-HO arrows over an abstract hom-family, with
fields for identities, composition, products, sums, exponentials where
available, functorial action, strength, constructors, and the chosen
recursion principle.

The inductive syntax would then be the initial instance of this
signature, while models and translations would be homomorphisms out of
that initial instance.  This could make the model infrastructure more
uniform without replacing the raw syntax by a tagless-final
presentation.  Law records could be factored along the categorical
structure they express: cartesian structure, cocartesian structure,
closed structure, functor/strength laws, and fold/paramorphism laws.

This direction fits the simply typed CwF and bifunctorial future-work
threads.  A CwF-style interface would organize contextual syntax, while
the algebraic operation records would organize the point-free target
categories and their models.  A mixed-variance type-operator interface
could later instantiate the same record structure for a richer notion of
functorial action.

# Future Work: PREC Completeness

The current Nat-instance development constructs the forward comparison:
PR-Nat programs form the category `PREC`, and `compile*` is the arrow
part of a functor from `PREC` into the finite-`Nat` subcategory of the
PR-FO target.  A natural completeness theorem would prove the converse
direction on morphisms: every PR-FO arrow

```text
vec Nat n -> vec Nat m
```

in the finite-`Nat` subcategory is represented, up to the generated
PR-FO equality, by an `m`-tuple of PR-Nat programs of arity `n`.
Equivalently, the functor from `PREC` to the finite-`Nat` target
subcategory should be full.

This would turn the current bridge into a precise representation
theorem for the Nat fragment of PR-FO.  Proving it likely requires a
normalization or definability argument for PR-FO arrows whose source and
target are finite products of `Nat`, showing that intermediate uses of
products, sums, and the polynomial `Nat` encoding do not define more
maps than ordinary primitive recursion on natural-number tuples.

# Future Work: CwF Connections

## Reusable Simply Typed CwF Interface

The contextual PR-FO and PR-HO calculi already have the shape of a
simply typed category with families.  Contexts are closed types,
substitutions are arrows into a context, terms in context are arrows out
of that context, the empty context is terminal, context extension is
product, and substitution is composition.  Because types are closed and
do not depend on terms, type reindexing is trivial.

A useful refactor would make this structure explicit as a reusable Agda
interface.  Such an interface would package:

- contexts;
- substitutions and their category laws;
- closed types;
- terms in context;
- the empty context;
- context extension by product;
- variables/projections;
- substitution of terms;
- equations or setoid laws for the above structure.

The contextual PR-FO and PR-HO calculi could then be instances of this
interface, and translations such as the System T elaboration could be
written against the interface where possible.  This would make the
connection with standard CwF terminology explicit without changing the
current point-free target categories.  It would also separate a reusable
typed-syntax layer from the particular primitive-recursion operations
that PR-FO and PR-HO add.

The existing compile/reify results between contextual and point-free
PR-HO are a good first test case for such an interface.  In the refactor,
these results should say that the contextual CwF-style presentation and
the point-free categorical presentation describe the same target
category, with equation preservation in both directions.

## Dependent CwF Story

A genuine dependent CwF would require a larger redesign.  Instead of
closed type codes, one would need families `Ty Gamma` indexed by
contexts, nontrivial reindexing of types along substitutions, and terms
whose types may depend on previous terms in the context.  The current
development deliberately avoids these issues: its type language is
simple, and its functor variables range over type codes rather than
term-indexed families.

For primitive recursion over dependent data, the type-code and model
interfaces would need corresponding dependent structure.  Possible
requirements include:

- type formers stable under reindexing;
- products, sums, exponentials, and inductive types in slices or in the
  comprehension category;
- dependent versions of `fmap` and `strength`;
- dependent initial algebras or W-types/inductive families;
- fold and paramorphism laws stable under substitution;
- logical relations stated over dependent families.

This is probably beyond the scope of the current paper.  The near-term
paper can mention the simply typed CwF reading as design context, while
the dependent version should remain future work unless the artifact is
refactored around a CwF interface first.
