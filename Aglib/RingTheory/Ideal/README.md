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

[SquareZeroUnits](SquareZeroUnits.lean) constructs the actual `1+x` units of a
square-zero ideal, identifies the additive ring kernel with the kernel of the
original map on units, and gives its restriction naturality. It also lifts
units over nilpotent ideal quotients.
[PowerQuotientSquareZero](PowerQuotientSquareZero.lean) proves that the actual
positive-level `factorPowSucc` kernel is square zero and that its map on units
is surjective. The kernel is the image of the original ideal power; no flat
tensor identification is used. These results feed the
[ring-sheaf unit sequence](../../Algebra/Category/Ring/Sheaf/README.md) and the
formal line-bundle lifting tower.

[ArtinReesInfMulSup](ArtinReesInfMulSup.lean), imported as
`Aglib.RingTheory.Ideal.ArtinReesInfMulSup`, proves `Ideal.exists_inf_mul_sup_pow_eq_mul`: for
ideals `I` and `𝔪` of a Noetherian ring there is `m ≥ 1` with `I ⊓ 𝔪 * (I ⊔ 𝔪 ^ m) = 𝔪 * I`.
Equivalently, for `J = I + 𝔪 ^ m` the map `I / 𝔪 I → J / 𝔪 J` is injective. It follows from
Mathlib's Artin–Rees lemma `Ideal.exists_pow_inf_eq_pow_smul`; no local or field hypothesis is
used. The consumer is the [Artinian-test criterion](../Smooth/ArtinianLifting.lean).
