# Noetherian scheme geometry

[DenseAffine](DenseAffine.lean) is a compatibility import of the sole
[general dense-affine owner](../DenseAffine.lean), documented in the
[parent property guide](../README.md). All four original native `Scheme`
declaration names remain available.

The primitive affine enlargement and dense-neighborhood statements require
only finitely many irreducible components. Compactness additionally gives
the finite dense-affine cover and dense common intersection.
`Scheme.exists_finite_dense_affine_cover` retains its actual `IsNoetherian X`
hypothesis and follows from those general statements. The broader owner
records these weakest hypotheses without classifying the primitive results
as Noetherian-only geometry; empty schemes are still included.

[LocallyNoetherianOver](LocallyNoetherianOver.lean): `Scheme.LocallyNoetherianOver S`, the full
subcategory of `Over S` on locally Noetherian schemes (all morphisms over `S`; property
`Scheme.locallyNoetherianOver S`), with inclusion `Scheme.locallyNoetherianOverInclusion` and the
instance `Scheme.LocallyNoetherianOver.isLocallyNoetherian`: the test schemes of Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §1, pp. 3–4.
