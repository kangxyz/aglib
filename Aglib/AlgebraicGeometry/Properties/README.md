# Scheme object properties

[Regular stalks](Regular/README.md) records regularity of the actual local rings,
its invariance under scheme isomorphisms and restriction to a source open, and
its affine comparison with regular rings. The
[geometric regularity](../Geometrically/Regular.lean) and smoothness criteria
consume this interface with their stated finiteness hypotheses.

[Normal](Normal/README.md) owns normal-stalk properties and their reducedness consequence; connected integrality additionally retains local Noetherianity. [IrreducibleComponents](IrreducibleComponents.lean) owns the weaker domain-stalk/component separation results. When every stalk is a domain, irreducible components are open if there are finitely many components; a separate theorem proves openness under local Noetherianity without a global finite-component hypothesis. The quasi-compact category and affine-induction principles below are separate general scheme interfaces.

This extends the object-property subject of Mathlib's native `AlgebraicGeometry/Properties.lean`. Morphism properties and their field-relative hypotheses have their own [Morphisms](../Morphisms/README.md) owner; the directory grouping does not change the types of the underlying Mathlib predicates.

[QuasiCompactCategory](QuasiCompactCategory.lean) defines the actual `Scheme.QuasiCompactSchemes` full category and its inclusion. [AffineInduction](AffineInduction.lean) gives `Scheme.AffineInduction.of_qcqs`: an isomorphism-invariant property with its affine case and compact binary-open-union closure follows on quasi-compact quasi-separated schemes. Union closure explicitly requires the property on both opens and their intersection; the induction does not manufacture the overlap premise. The compact-open and separated variants retain their corresponding compactness/separation hypotheses.

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
under [Proper](../Morphisms/Proper/README.md); it does not prove Chow's lemma
or coherent cohomological finiteness. The mathematical references are
[Stacks, suitable affine neighborhoods](https://stacks.math.columbia.edu/tag/01ZU)
and the opening of
[Stacks, Chow's lemma](https://stacks.math.columbia.edu/tag/02O2).

The sole implementation is `Properties.DenseAffine`, because its primitive
statements need only finite irreducible components, with compactness added
for the finite-cover conclusion. The former
[Noetherian import](Noetherian/DenseAffine.lean) is a thin compatibility
module. All four native `Scheme` declarations and their statements are
unchanged. The implementation was moved byte for byte, with SHA-256
`936ace3003edccb7f026470e640687adb3bb1ad244e32b2795585c4b8440ebe4`.
