# Future Work: Positive Higher-Order Type Operators

The current PR-HO type syntax restricts function domains to closed
types:

```agda
_`=>_ : forall {n} -> Ty HO 0 -> Ty HO n -> Ty HO n
```

This avoids mixed variance.  If a type expression has the shape
`A X => B X`, then occurrences of `X` in `A X` are contravariant in the
whole type.  Given an arrow `f : T -> U`, functoriality for the whole
type would require a map

```text
(A T => B T) -> (A U => B U)
```

The codomain side is covariant: from `f` one can map `B T -> B U`.
The domain side, however, would require a map `A U -> A T` in order to
feed an `A U` argument to a function expecting `A T`.  Thus merely
allowing positive occurrences in the function argument is not enough:
positive occurrences inside a function domain become negative in the
whole function type.

A clean generalization would track variance in the type syntax.  In
such a polarized syntax:

- products and sums preserve variance;
- in `A => B`, variances in `A` are flipped and variances in `B` are
  preserved;
- `ind G`, `fmap G`, and `strength G` are available only when the
  relevant variable is positive overall.

With this discipline, function domains may mention variables when the
whole type operator remains covariant.  For example, a continuation-like
type `(X => R) => R` is positive in `X` overall: the inner function
domain flips once, and the outer function domain flips again.

Categorically, this changes the development from ordinary covariant type
operators to mixed-variance type expressions.  Exponentials are
bifunctorial as `(-)^(-) : C^op x C -> C`, not covariant in both
arguments.  The current closed-domain restriction avoids this machinery
and guarantees that every `Ty HO n` acts covariantly in its variables.

This extension is possible, but it would be a substantial refactor.  It
would require a polarized or variance-indexed `Ty`, variance-aware
substitution and action, and corresponding changes to `fmap`,
`strength`, recursion, equations, model interfaces, and translations.
The model obligations would also become stronger, because models would
need initial-algebra or recursion structure for the larger class of
positive higher-order functors.

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
