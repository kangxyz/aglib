# Finite normalization of complete local curves

`integralClosure.finite_of_complete_local_dimLE_one R K L` proves
`Module.Finite R (integralClosure R L)` when `R` is a complete Noetherian
local domain of dimension at most one, `K` is its fraction field, and
`L/K` is any finite field extension. Completeness is for the actual
maximal ideal of `R`. The algebra actions form the declared tower
`R → K → L`; the normalization is the literal `integralClosure R L`.
No separability hypothesis is imposed, so purely inseparable extensions
are included. The field case is included.

Two general suppliers precede the normalization specialization.
`Algebra.IsIntegral.isNoetherianRing_of_rank_lt_aleph0` proves that an
integral domain algebra `B` of finite cardinal rank over a Noetherian
domain `R` of dimension at most one is Noetherian, assuming the
`R`-action is torsion-free. This action hypothesis preserves the
inclusion of the base. There is no initial `Module.Finite R B` or
`IsNoetherianRing B` assumption.

For every nonzero `B`-ideal `J`, integrality supplies a nonzero element
`a ∈ J ∩ R`. The scalar-quotient length bound makes `B / a B` a finite
length `R`-module. Its Noetherianity transfers to `B`-scalars. The image
of `J` in that quotient is finitely generated, and its kernel is the
principal ideal `a B`. The native finite-generation extension lemma
therefore proves `J` finitely generated. This is the integral-algebra
case of Krull–Akizuki, proved before module finiteness.

`Algebra.IsIntegral.finite_of_isAdicComplete_maximalIdeal` adds locality
and completeness of `R`. For a nonzero `a` in its maximal ideal `m`,
the finite module `B / a B` surjects onto `B / m B`. Every maximal
ideal of `B` contracts to `m` by integrality, giving `m B ⊆ Jac(B)`.
The lower adic finite-generation criterion derives separatedness from
the proved Noetherianity of `B` and lifts generators using completeness
of their coefficients. Completeness of `B` is never assumed. When
`m = 0`, `R` is a field and finite rank gives finiteness directly.

The normalization specialization bounds its rank using its actual
inclusion in `L` and the fraction-ring rank comparison. The proof does
not import the separate finite-separable-normalization theorem.

`integralClosure.finite_of_complete_local_reduced_dimLE_one R Q`
extends finiteness to a reduced complete Noetherian local ring of
dimension at most one and its literal total quotient ring
`[IsFractionRing R Q]`. The construction keeps every minimal-prime
quotient and its original coefficient map.

`quotient_mk_ne_zero_of_nonZeroDivisor` proves that a non-zero-divisor
of `R` has nonzero image modulo each minimal prime. This lemma needs
neither reducedness nor Noetherianity. The quotient is a domain, so its
fraction-field image is a unit. This supplies the unit condition in
`IsLocalization.liftAlgHom`, which constructs `toMinimalPrimeFraction`.
Its coefficient equation is `toMinimalPrimeFraction_algebraMap`.
`toMinimalPrimeNormalization` restricts this actual map to the literal
normalizations, using the mapped monic equation and the quotient scalar
tower. `coe_toMinimalPrimeNormalization` identifies its underlying
fraction-field map.

`toMinimalPrimeFractions` and `toMinimalPrimeNormalizations` take the
products over the actual type `minimalPrimes R`. For a reduced base,
the coefficient kernel of the fraction product is the intersection of
the minimal primes, hence zero. The native localization injectivity
lemma then handles the denominators in `Q`. This proves the two
injectivity theorems without assuming a normalization/product
isomorphism.

For each prime quotient `R / p`, the private component supplier derives
Noetherianity and locality from the actual quotient map and bounds its
dimension by that of `R`. The quotient is a finite `R`-module, so the
existing finite-module completeness theorem makes it complete for the
extended maximal ideal. The equality
`map_maximalIdeal_of_surjective` identifies that ideal with the actual
maximal ideal of `R / p`. The domain theorem makes its normalization
finite over `R / p`, hence over `R`. Finiteness of the minimal-prime
set and the injective product map then give finiteness of the original
normalization as a submodule over the Noetherian base.

`quotient_isFiniteLength_of_complete_local_reduced_dimLE_one` applies
the existing colength theorem to this proved finite normalization and
the actual original coefficient map. Finite colength applies here to
normalization in the original total quotient ring. For a larger field
extension `L/K`, the quotient of the normalization by `R` generally
has positive generic rank. These results prove no finite-normalization
theorem for a two-dimensional graph and no surface-resolution theorem.

This is new source over Aglib base
`22f7532679eec4295167fcf885cf8b1b0981d899`, with Mathlib pin
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The source-side route is
Stacks Project Lemma 10.119.12, [Tag 00PG](https://stacks.math.columbia.edu/tag/00PG),
and its nonzero ideal-contraction input, Lemma 10.30.8,
[Tag 0H7L](https://stacks.math.columbia.edu/tag/0H7L), inspected on
2026-10-23. The implementation uses the native integral-contraction
theorem and the lower scalar-quotient proof, not an assumed theorem
family. These source checks are separate from independent proof review.
