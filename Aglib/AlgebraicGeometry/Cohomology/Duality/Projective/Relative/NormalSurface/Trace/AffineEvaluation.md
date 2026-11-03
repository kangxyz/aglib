# Local inverse trace and affine evaluation

Source: [AffineEvaluation.lean](AffineEvaluation.lean).

For qcqs f, quasicoherent M and L, and an actually invertible trace
`tau : f_*M → L`, the localized pullback is the original square pullback
comparison, followed by pullback of the inverse coefficient isomorphism,
sheafification of the inverse localized trace, and original affine evaluation.

The coefficient isomorphism is tilde of the existing stalk/local-spectrum
sections isomorphism followed by the original tilde counit. The evaluation is
the pulled-back tilde counit followed by the original geometric counit.
`canonicalLocalInverseTraceSections` is exactly rho inverse followed by the
inverse original pushforward-sections isomorphism. The proved normalization
identifies this map with the original ordinary base-change mate on sections.
Naturality of the original tilde counit upgrades it to the stated sheaf-map
equality; no faithfulness of global sections on a non-affine scheme is assumed.

No finite or complete initial-base hypothesis is imposed on the later stalk.
Invertibility of tau is explicit, not a consequence asserted for arbitrary
proper maps.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/Trace/PointBlowupFrame](PointBlowupFrame.md).
