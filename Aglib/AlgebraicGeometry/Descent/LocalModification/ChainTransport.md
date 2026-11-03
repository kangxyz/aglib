# Exact chain transport through the actual base isomorphism

Source: [ChainTransport.lean](ChainTransport.lean).

`NormalizedPointBlowupChain.transportIso` produces a literal normalized-point
chain over the new integral base, with the image of each prescribed centre,
exactly the original length, and a terminal isomorphism whose structural
triangle is the original map composed with the given base isomorphism.

It uses `normalizedPointLocalizationIso` on the actual base isomorphism at
each step. This is needed to move a next local chain through the actual
stalk-ring isomorphism after earlier disjoint supported chains, before
concatenating native chains. It does not mistake a chain followed by an
arbitrary isomorphism for a native chain by definitional equality.

Finite-family serial assembly is not asserted
by this lemma alone.

Direct consumers: [AlgebraicGeometry/Surfaces/Resolution/PointBlowupChain/NormalizedPresentation](../../Surfaces/Resolution/PointBlowupChain/NormalizedPresentation.md).
