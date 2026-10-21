# Canonical Cartier ideal constructions

[Interfaces](Interfaces.lean) records the codimension-one, avoidance, product
and DVR-fibre statements on the original native kernel ideal modules.
[Restriction](Restriction.lean) applies their actual comparison maps.

[Avoidance](Avoidance.md) proves `integralAvoidanceCartierPullback`: for an
integral source whose image is not contained in a Cartier divisor, the
canonical ideal pullback map is invertible. It needs neither flatness of the
map nor Noetherianity.

[Product](Product.md) proves `cartierIdealTensorProduct`, including the exact
multiplication and inclusion triangle, and `cartierSumIdealEqualsUnion`.
The latter retains Cartierness of the actual intersection on the second
divisor. Its pointwise forms allow an arbitrary second closed ideal.

[DVRFibre](DVRFibre.md) constructs `flatDVRFibreIdealIso` for the actual closed
fibre of a flat scheme over a DVR and supplies `flatDVRFibreIdealTrivial`.
Its comparison preserves the literal fibre projection and ideal inclusion.
The lower [flat-base comparison](../BaseChange/FlatMorphism.md) applies to
arbitrary affine vertical maps and flat base morphisms.

The generic [stalk-kernel criterion](../Invertible/StalkKernel.md) turns
singleton bases of the actual stalk-map kernels into local rank one of the
original ideal module on a locally Noetherian ambient scheme.
[Factorial](../Invertible/Factorial.md) derives these bases from explicit
factorial domain structures on every actual ambient stalk and the height-one
condition for an integral closed subscheme. It has no dimension bound.
[RegularSurface](../Invertible/RegularSurface.md) retains the bounded
regular-local dimension-at-most-two specialization and its exact public
statement, using that same shared criterion.

[Regular](Regular.md) derives the required domain and unique-factorization
structures from regularity of every actual ambient stalk. It supplies the
original `regularCodimOneIdealInvertible` family without a dimension bound or
an additional UFD premise, retaining integral closed source, locally
Noetherian ambient scheme, and height-one actual stalk kernels.

The separate smooth-relative-curve supplier belongs to
`EffectiveCartierDivisor/Smooth/Ideal.lean`. Relative graph and base-change
adapters retain the same original ideal module and canonical maps.

Interface source: R5 packet revision `f8a3314ddecffcada2ec721d26d56a937bed9690`,
`R5Lab.Aglib.AlgebraicGeometry.Divisors.Cartier.{Interfaces,Restriction}`.
