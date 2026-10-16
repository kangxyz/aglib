# Derived categories, Ext and comparison units

[Ext](Ext/README.md) gives the original exact-functor/source-precomposition
comparison and its all-degree acyclic-injective comparison criterion. It
retains arbitrary Ext size universes and does not assume preservation of
injective objects.

[Plus](Plus/README.md) gives actual short-exact triangles, their maps, bounded term comparisons and a one-sided derived contraction. [RightDerivedFunctorPlus](RightDerivedFunctorPlus/README.md) supplies the actual identity/composition comparisons with their installed units.

The objects and localization functors are Mathlib's bounded-below derived categories. Abelian, derived-category and enough-injective assumptions are retained by the particular constructor; existence of an injective model is not silently added to a result which needs only a short exact sequence. Scheme Godement/direct-image and derived projection-formula consumers use these exact maps and unit equations.

[TStructure](TStructure/README.md) supplies the unique original-homology
normalization of concentrated derived objects and its coefficient
naturality. It is shared by Postnikov layers and geometric purity;
no enough-injectives or chosen-representative hypothesis is imposed.
