# Original canonical-stalk comparisons

Source: [CanonicalStalk.lean](CanonicalStalk.lean).

This lower leaf contains the unchanged original quotient-chart ambient-linear
Ext comparison, original global-stalk ambient-linear Ext comparison, and
actual quotient-stalk dimension normalization formerly located in
`Trace/Localization.lean`. Original names, statements, coefficient lines,
restriction/stalk maps and proof bodies are preserved exactly.

The Ext degree is the actual embedding integer `n`. Ambient dimension is
`n + dim(local source)`. Original-stalk transport uses the actual open-stalk
ring isomorphism and native restriction-of-scalars comparison. No later
stalk is assumed finite over or complete over the original regular base.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/Trace/Localization](Trace/Localization.md), [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/Trace/StalkAction](Trace/StalkAction.md).
