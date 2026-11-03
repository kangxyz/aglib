# Original dual map into a pulled-back dual line

Source: [DualMapToPullback.lean](DualMapToPullback.lean).

For `f : Y → X`, the original line `I` on `X`, an arbitrary `J : Y.Modules`,
and an arbitrary original arrow `e : f*I → J`, `dualMapToPullback` constructs
`J∨ → f*(I∨)` using the existing `pullbackPairingOfEquiv`. Its defining pairing
is `(id ⊗ e) ≫ evaluationSheaf`; the complete pairing equation is proved by
the same equivalence's inverse law.

`transpose_dualMapToPullback` starts with original coefficients `α : I → O_X`,
`β : J → O_Y` and their genuine square
`e ≫ β = f*(α) ≫ pullbackUnitIso.hom`. It concludes that `transpose β` followed
by this same dual map is `pullbackUnitIso.inv ≫ f*(transpose α)`.
The proof uses the native arbitrary-module `InternalHom.transpose_evaluation`,
tensor functoriality, original left-unit naturality, and the original pulled
transpose evaluation law. It copies no tensor/Hom or inverse backend.

Only `I` is a line. There is no line, QC, finite-presentation or invertibility
requirement on `J`, no condition on `f`, and no inverse of `e` or the resulting
map. Original sheaves, maps, scalar actions and universe are retained.

The geometric application sets `e` to the existing `idealPullbackMap` and its
coefficient square to `idealPullbackMap_inclusion`. The transposes then are the
actual positive exceptional sections. The pairing and transpose equations apply to that same geometric
coefficient square without adding a line hypothesis on J.

Direct consumers: [AlgebraicGeometry/Blowup/Differentials/PairIdeal/OpenCentre](../../../Blowup/Differentials/PairIdeal/OpenCentre.md), [AlgebraicGeometry/Blowup/Differentials/PairIdeal/OpenTransport](../../../Blowup/Differentials/PairIdeal/OpenTransport.md).
