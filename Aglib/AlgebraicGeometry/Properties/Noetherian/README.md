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
