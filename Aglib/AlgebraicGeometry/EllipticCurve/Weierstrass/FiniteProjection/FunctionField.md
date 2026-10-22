# The finite separable extension of the original fraction fields

The base is an original local domain `R`, expressed by `[CommRing R]`,
`[IsDomain R]` and `[IsLocalRing R]`. For every literal `W : WeierstrassCurve R`,
the source field is exactly `FractionRing (Polynomial R)` and the target field
is exactly `FractionRing (Projective.affineRing W)`. The target ring is the
same native `W.toAffine.CoordinateRing`. Its domain instance is supplied by
Mathlib's actual Weierstrass coordinate-ring theorem for domain bases; it is
not an added generic-integrality premise. No discriminant condition is needed.

`FiniteProjection.fractionMap W` is the native fraction-ring lift of the
original `projectionMap W` followed by the native target localization.
`fractionMap_algebraMap` is the exact commuting equation for every original
polynomial. `fractionMap_div` retains its numerator and denominator.
`fractionMap_X` maps the original polynomial variable to the original x- or
y-coordinate, according to the same original unit test on two. `fractionMap_C`
preserves the original R-constants.

The scalar structures `coefficientFractionAlgebra W` and `fractionAlgebra W`
are explicit values. The coefficient action uses the native inherited
fraction-ring algebra after locally selecting the original projection on B.
No second global polynomial-algebra instance is installed. The two public scalar-tower theorems retain the actual triangles
through the original affine ring and the original polynomial fraction field.
Their actions are explicitly the corresponding algebras' own `toSMul` values;
this avoids the separate global x-action inherited by standalone localization
scalar instances. Consumers install `fractionAlgebra W` locally for the field statements.

`fraction_finrank W` applies the native simultaneous fraction-ring finrank
identity to those same scalar triangles. Its value is exactly the frozen
core's `projectionDegree R`, namely two when two is a unit in R and three
otherwise. `fraction_finiteDimensional W` follows from this positive rank.
This step transfers the displayed rank to the actual field map; the finite
algebra trace retraction alone is not used as a substitute for that bridge.

`projectionDegree_fraction_isUnit` maps the same degree unit from R[T] to its
native fraction field. `fraction_trace_one W` proves that the actual field
trace of one equals this degree. It is nonzero. Mathlib's theorem that a
nonseparable field extension has zero trace then gives
`fraction_isSeparable W`. The single endpoint `fraction_extension W` returns
finiteness, exact degree and separability under the same explicit scalar
structure.

These results need no Noetherian, excellent, DVR, perfectness, characteristic,
nonsingularity or coefficient-field assumption. They concern the full original
fraction-field extension and retain all original maps. They do not divide the
trace of a completed local factor by the full degree. They prove no regularity,
rational-singularity property, uniform H¹ bound or resolution termination.
Those remain separate obligations for the singular Weierstrass resolution
consumer.
