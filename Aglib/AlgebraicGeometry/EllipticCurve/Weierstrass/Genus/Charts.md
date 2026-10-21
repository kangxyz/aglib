# The original Weierstrass chart quotient

`Charts.lean` supplies the monic cubic bases, Laurent overlap and canonical
homogeneous-localization comparisons used by [Genus](../Genus.md).
The actual affine coordinate ring is identified with its cubic presentation
over `R[y]`; the existing infinity ring has its cubic presentation over
`R[v]`. Their overlap maps retain `x=u/v` and `y=1/v`.

Over every nontrivial commutative ring, `overlapChartQuotientEquiv` identifies
the quotient of the actual overlap ring by the sum of the two chart images
with `R`. Its forward map extracts the coefficient of `u²/v`. The proof uses
the explicit monomial bases and their original restriction images.

`homogeneousOverlapEquiv` identifies the same overlap with the homogeneous
localization at `YZ`. `homogeneousOverlapEquiv_affineMap` preserves the
original affine restriction map. Over a field, `basicOpen_constantSection`
identifies the structural constants with their canonical homogeneous
fractions. These constructions require no discriminant or smoothness
hypothesis. The original H¹ comparison and genus theorem belong to the
higher `Genus.lean` consumer.
