# A chosen frame at the original generic point

Source: [GenericFrame.lean](GenericFrame.lean).

`normalSurfaceCanonicalGenericFrame` gives a linear equivalence from the
stalk of the actual chosen-embedding canonical sheaf at the original generic
point to `X.functionField`, over that same native function field.

The full existing normal-surface telescope is retained: a closed projective
embedding of an integral scheme over a regular local domain, a dominant
structural map, normal original stalks, dimension at most two, a specified
finite coordinate equivalence, and finiteness of the original generic-image
base map. The function field is literally the original generic stalk.
Its field structure gives semisimplicity, module and categorical injectivity,
and self-injective dimension zero. The construction then invokes
`normalSurfaceCanonicalStalkLinearEquivOfSelfInjectiveDimension` once, only
at the generic point.

The frame is chosen, not canonically normalized. Later fraction embeddings
must retain this same choice and the original germ maps. No supplied rank,
frame, rationality, or Gorensteinness of singular stalks is used. This result
does not trivialize the canonical sheaf on an open set or at a singular
point. Canonical torsion-freeness remains owned by `CartierRegularity`; no
parallel proof or unused class packaging is added here.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/StalkEmbedding](StalkEmbedding.md).
