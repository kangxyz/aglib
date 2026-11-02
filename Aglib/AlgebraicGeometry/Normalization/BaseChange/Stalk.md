# Relative normalization at the original target stalk

Source: [Stalk.lean](Stalk.lean).

For a qcqs `f : X → S` and any original point `s : S`,
`normalizationPullback_isIso_fromSpecStalk` proves invertibility of the
native comparison `f.normalizationPullback (S.fromSpecStalk s)`.
The actual stalk, germ and normalization arrows are retained.
There is no affine-base, Noetherian, normality, dimension, excellence or
completion hypothesis in this general theorem.

`normalizationPullback_isIso_fromSpecStalk_of_isAffine` gives the affine
case using the original `ΓSpecIso`, stalk localization and affine
normalization comparison. The general proof chooses an actual affine
neighborhood and pastes these same comparisons through the open
inclusion. Normalized point localization and supported-chain
globalization use this original stalk comparison.

Direct consumers: [AlgebraicGeometry/Normalization/BaseChange/FlatPreimmersion](FlatPreimmersion.md).
