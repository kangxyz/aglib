# Full marked data through the original ring equivalence

Fix any ring equivalence between two original local commutative rings,
with independent source and target universes. `maximalIdealEquivMap` applies
that actual equivalence to an original maximal-ideal element; membership
comes from the native local-hom theorem.

`doubleLineChildCotangentKernel_ringEquiv` specializes the unique entire
cotangent-polynomial map/kernel square to the two actual maximal ideals.
The coefficient equivalence is proved equal to the original
`IsLocalRing.ResidueField.mapEquiv`, whose forward arrow is the original
`ResidueField.map`. Thus no arbitrary residue-field identification is chosen.
The normalized full square kernel is derived by the same polynomial
coefficient map and native ideal-image laws.

`CubicCoefficients.map` applies the same original homomorphism to all ten
coefficients. `CubicRelation.map` transports the true equation and its actual
fourth-order remainder. `MarkedCubic.map` and `TripleEntryData.map` transport
all their fields: actual maximal-ideal generators, full canonical kernel,
true equations, remainder/ideal-power membership, units and the original
simple-root residue conditions. Exact other, square, remainder, distinguished
coefficient and original residue-map equations are exposed for consumers.

This leaf does not supply a transported marker as a hypothesis or replace a
scheme stalk with an abstract localization. A later actual-stalk consumer
uses the inverse of the already constructed native stalk isomorphism and its
proved original stalkScalar identity. Initial marking, marked entry,
Gorenstein preservation and termination remain separate genuine obligations.
