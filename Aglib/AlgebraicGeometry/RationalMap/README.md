# Rational coordinates and graph closures

[Graph](Graph.lean), in `Scheme`, constructs the literal graph map from an open
of a field scheme into a fibre product and then takes its actual schematic
image. It retains both projections and their triangles. Properness of each
projection has its own properness hypothesis on the opposite field scheme.
Image integrality, dominance, Noetherianity and the isomorphism over the
original open retain their separate displayed assumptions.

This is a graph-closure construction over a field. It does not construct a
common regular domination or a graph closure over an arithmetic trait. The
native curve projectivity constructions use this exact field graph.

The proof reuses the actual schematic-image integrality and the open-section
restriction theorem from their lower native owners.

## Denominator and base ideals

[BaseIdeal](BaseIdeal.md), in `Scheme.RationalCoordinates`, starts with a finite
family in the original function field of an integral scheme. Its actual
denominator ideal and kernel module retain the simultaneous denominator and
numerator equations. The base ideal is the image of the original numerator
row, and its coordinate maps from the denominator module form an epimorphic
row with the same index. On nonempty affine opens and actual stalks, the
comparisons use the original fractional-coordinate span and its integral
product with the denominator ideal. They do not replace nonaffine section
ideals by affine quotient formulas.

The lower [finite fractional denominators](../../RingTheory/FractionalIdeal/Denominator.md)
supply the original common-denominator and numerator maps. Over a GCD domain,
a finite coordinate family containing one has a nonzero principal denominator;
this retains the actual coefficient map and specified coordinates.

If an original coordinate is one, the base ideal is nonzero and contains the
denominator ideal. On a locally Noetherian integral scheme with regular
actual stalks, `denominatorModule_isLocallyRankOne` makes the actual denominator
kernel module a line module, with no dimension bound. On a globally Noetherian
regular integral scheme with actual stalk dimensions at most two,
`baseIdeal_isArtinian_subscheme` makes the original base-ideal quotient
Artinian; finite local colength is derived from regularity and primitivity.
These endpoints construct the coordinate ideals and maps. Extension of a
given rational projective morphism remains a separate consumer.
