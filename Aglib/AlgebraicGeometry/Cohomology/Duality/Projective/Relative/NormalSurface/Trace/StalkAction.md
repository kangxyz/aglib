# Original local source action on the canonical stalk

Source: [StalkAction.lean](StalkAction.lean).

This leaf upgrades the existing actual ambient-linear quotient-stalk map to
the source stalk ring, keeping exactly its additive equivalence. The actual
closed-immersion stalk map is surjective. Each source scalar therefore lifts
to the ambient ring, where linearity was already proved; the target action
is the native Yoneda/coinduction action supplied by Coinduction.SourceAction,
whose restriction equals the unchanged ambient Ext action.

The original global canonical stalk is transported through the original
restrictModuleStalkIso. Its own local-ring action is retained by restriction
along the actual open-stalk ring homomorphism, rather than identifying the
original scheme with a quotient chart silently. A further comparison uses the
original derived-coinduction homology-to-Ext equivalence and its inverse to
reach the actual source-module homology used by the injective-dimension owner.
No ordinary coextension exactness or projective quotient assumption occurs.

The ambient coefficient line, embedding degree and actual original stalk are
retained. This leaf alone asserts neither finite injective dimension nor
intrinsic Gorensteinness; those require the separate lower concentration and
Baer argument and coefficient-line normalization.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/Trace/StalkInjectiveDimension](StalkInjectiveDimension.md).
