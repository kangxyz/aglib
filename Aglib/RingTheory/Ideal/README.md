# Ideal and prime interfaces

[MinimalPrime](MinimalPrime/README.md) studies actual extension/contraction of minimal primes under flatness or supplied going down. These conditional ring results feed support/local-length and multiplicity arguments.

The objects remain Mathlib ideals and prime spectra. Normality/integrality supplies going down only through the precisely stated variant; it is not an automatic property of an arbitrary algebra.

[RegularPrincipal](RegularPrincipal.lean), imported as `Aglib.RingTheory.Ideal.RegularPrincipal`, relates actual singleton ideal bases and regular principal generators over arbitrary commutative rings. Its nonzero-ideal principal-domain variant retains its domain and principal-ideal-ring hypotheses.

[InvertiblePrincipal](InvertiblePrincipal.lean), imported as `Aglib.RingTheory.Ideal.InvertiblePrincipal`, proves `Ideal.isSMulRegular_of_invertible_span_singleton`: a generator of a principal ideal that is an invertible module is regular. No Noetherian or domain hypothesis is used.

[CoordinateDisplacement](CoordinateDisplacement.lean) and
[HeightOne](HeightOne.lean) supply coordinate-ideal and minimal-prime height
interfaces. The latter is consumed by the conditional
[FlatDVR component construction](../../AlgebraicGeometry/Stalk/FlatDVR/README.md),
which still requires its actual special-fibre kernel input.

[RegularPrincipal/BaseChange](RegularPrincipal/BaseChange.md) proves the
canonical extended-kernel map invertible when the original kernel and its
image have the displayed regular generators. It keeps the actual commuting
ring square. [Intersection](RegularPrincipal/Intersection.md) proves regular
principal cancellation against an arbitrary ring kernel; these lower results
feed the native Cartier avoidance and product constructions.
