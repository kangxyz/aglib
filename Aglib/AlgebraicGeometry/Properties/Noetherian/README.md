# Noetherian scheme geometry

[DenseAffine](DenseAffine.lean) proves
`Scheme.exists_isAffineOpen_superset_genericPoints`: when the actual scheme has
finitely many irreducible components, every affine open is contained in an
affine open containing all generic points. It adds affine neighborhoods inside
the complement of the other components and uses Mathlib's
`IsAffineOpen.iSup_of_disjoint` for their finite disjoint union. No separation,
reducedness, irreducibility or ring-Noetherian hypothesis is needed for this
statement.

`exists_dense_isAffineOpen_mem_of_finite_irreducibleComponents` gives a dense
affine neighborhood of every point. With `CompactSpace X`,
`exists_finite_dense_affine_cover_of_finite_irreducibleComponents` gives a finite
family of actual opens, each affine and dense, whose supremum is top and whose
common intersection is dense. Each member contains the original
`genericPoints X`. `exists_finite_dense_affine_cover` supplies the same result
for every Noetherian scheme, including the empty scheme.

The finite-component proof only needs ordinary topology and the actual affine
open basis. It is the dense-cover input to the proper graph-product construction
under [Proper](../../Morphisms/Proper/README.md); it does not prove Chow's lemma
or coherent cohomological finiteness. The mathematical references are
[Stacks, suitable affine neighborhoods](https://stacks.math.columbia.edu/tag/01ZU)
and the opening of
[Stacks, Chow's lemma](https://stacks.math.columbia.edu/tag/02O2).
