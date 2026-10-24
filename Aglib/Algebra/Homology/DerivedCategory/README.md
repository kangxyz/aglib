# Derived categories

[KInjective](KInjective/README.md) compares the actual homotopy and derived Hom
maps at supplied K-injective targets, gives original chain representatives and
additive-functor action there, and retains chain adjoints in the target-sensitive
adjunction Hom equivalence. Object, morphism and derived-model universes remain
independent; no global derived-category instance is added.

[Plus](Plus/README.md) gives actual short-exact triangles, their maps, bounded term comparisons and a one-sided derived contraction. [RightDerivedFunctorPlus](RightDerivedFunctorPlus/README.md) supplies the actual identity/composition comparisons with their installed units.

The objects and localization functors are Mathlib's derived categories. Abelian, derived-category and enough-injective assumptions are retained by the particular constructor; existence of an injective model is not silently added to a result which needs only a short exact sequence. Scheme Godement/direct-image and derived projection-formula consumers use these exact maps and unit equations.

The [K-projective family](KProjective/README.md) gives original chain
representatives and homotopies for derived arrows from K-projective sources,
without term bounds. [Minus](Minus/README.md) proves that the actual
bounded-above chain category localizes to Mathlib's existing ambient
`DerivedCategory.Minus`, without enough-projective or enough-injective hypotheses.

[Ext](Ext/README.md) gives the original exact-functor/source-precomposition
comparison and its all-degree acyclic-injective comparison criterion. It
retains arbitrary Ext size universes and does not assume preservation of
injective objects.

[TStructure](TStructure/README.md) supplies the unique original-homology
normalization of concentrated derived objects and its coefficient
naturality. It is shared by Postnikov layers and geometric purity;
no enough-injectives or chosen-representative hypothesis is imposed.

## Unbounded right-derived suppliers

[UnboundedRightDerived](UnboundedRightDerived/README.md) constructs original
right-derived functors from native K-injective resolutions. Its Grothendieck
specialization uses the actual functorial
[K-injective replacement](KInjective/Existence/Tower/README.md), with natural
monic quasi-isomorphism, rather than a supplied-replacement premise.
Conditional lower interfaces retain their explicit hypotheses. This is
derived existence, not a geometric proper-exchange or finite-dimensional
acyclic-computation theorem.
