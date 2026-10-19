# Regular actual local rings

[Basic](Basic.lean) defines `Scheme.RegularStalks X`: every actual stalk of `X`
is a regular local ring. The property is invariant under scheme isomorphisms
and pulls back along open immersions. For a Noetherian commutative ring,
`regularStalks_spec_iff` identifies it with `IsRegularRing`.

This stalk property alone does not assert that the scheme is locally Noetherian.
The [geometric regularity criterion](../../Geometrically/Regular.lean) and
[smoothness criterion](../../Morphisms/Smooth/GeometricRegularity.lean) retain
the local finite-type or finite-presentation hypotheses needed there.
