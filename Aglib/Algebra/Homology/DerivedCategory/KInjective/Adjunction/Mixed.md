# Mixed projective and injective derived Hom

`CategoryTheory.Adjunction.cochainDerivedHomEquivOfMixed` applies to an
additive adjunction between abelian categories equipped with derived
categories, a native K-projective source complex, and a native K-injective
target complex. It gives an additive equivalence between the two original
derived Hom groups. The left adjoint need not be exact.

The construction uses the original homotopy adjunction, localization from
the K-projective source, and localization into the K-injective target.
Its `_map` and `_symm_map` equations retain the original chain adjunction in
both directions. In particular, it imposes no K-injectivity condition on
the image of the target under the right adjoint.

The current consumer is the bounded finite-source comparison in
`AlgebraicGeometry/Cohomology/Proper/ResidueVanishing`.
