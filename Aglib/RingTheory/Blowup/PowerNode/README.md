# Saturated charts of the literal power-node algebra

The namespace `PowerNode.Rees` uses `PlaneNode.Ring c`, the actual algebra
R[U,V]/(UV-c). [Saturated](Saturated.lean) proves the domain and injective
localization facts, defines the centre (U,V,pi), and constructs actual outer and
middle blowdown ring maps. General definitions work over commutative rings.
The domain and chart-injectivity results retain the original domain/UFD and
nonzero scalar hypotheses; they are not restricted to DVRs.

[Charts](Charts.lean) identifies the actual saturated subalgebras in the
U-, V- and pi-localizations for UV = pi^(m+2). Both outer chart rings are
`PlaneNode.Ring pi`; the middle ring is `PlaneNode.Ring (pi^m)`. The equivalences
retain their actual base-map equations. These are generated subalgebras inside
the original localizations, so no unsaturated presentation or quotient torsion
is introduced.

[Overlaps](Overlaps.lean) gives both outer-middle localization equivalences,
the outer-outer transition and the actual triple-overlap equation. Its DVR
specializations retain the irreducible-uniformizer hypothesis while reusing the
stronger UFD/nonzero-scalar algebra.

The canonical [saturated chart](../../Localization/Away/SaturatedChart.lean) and
[plane-node algebra](../../PlaneNode/README.md) are reused literally. Global
blowup existence, a geometric affine atlas and a resolution scheme remain
separate geometric obligations in
[AlgebraicGeometry/Blowup](../../../AlgebraicGeometry/Blowup/README.md).
