# DVR criteria in dimension one

Import `Aglib.RingTheory.DiscreteValuationRing.DimensionOne`.

`IsDiscreteValuationRing.of_isIntegrallyClosed_of_dimLE_one` proves that
a normal Noetherian local domain of dimension at most one is a DVR when
it is not a field. The dimension bound makes the ring Dedekind, and the
native local DVR characterization applies. The nonfield hypothesis is
essential because the native DVR convention excludes fields.

`IsDiscreteValuationRing.of_isRegularLocalRing_of_dim_eq_one` proves
that a regular local domain of dimension exactly one is a DVR. The
native regular-local criterion gives cotangent-space dimension one,
and the cotangent DVR characterization finishes the proof. Both
criteria are proved at an abstract ring carrier before specialization.

`IsAssociatedPrime.mem_of_quotient_span_singleton` shows that an
associated prime of the actual quotient A/(x) contains its original
equation x. The equation annihilates the quotient module and therefore
belongs to the radical annihilator of an associated witness. This
statement requires neither Noetherianity nor normality.

`IsAssociatedPrime.isDiscreteValuationRing_atPrime_of_principal`
applies to a normal Noetherian domain A, nonzero x, and an actual
associated prime p of A/(x). It proves that the ambient
`Localization.AtPrime p` is a DVR. No global dimension bound or
locality of A is assumed. The original equation lies in p, so p is
nonzero. The existing associated-prime height theorem gives height at
most one, hence exactly one. Noetherianity and integral closedness
localize along the original map. The actual localization has dimension
one and is not a field, so the first criterion applies.

`IsRegularLocalRing.isDiscreteValuationRing_atPrime_of_minimal_principal`
handles the regular-ambient alternative. It assumes a Noetherian
domain A, nonzero x, p minimal over the original ideal (x), and regularity
of the ambient A_p. The principal ideal theorem bounds the height by
one, and nonzero x excludes height zero. The second criterion applies
to that same native localization. Normality of A is not a premise.

The current consumer is the explicit DVR input of the
[associated-prime completion criterion](../AdicCompletion/AssociatedPrimeCriterion.md).
For normal local normalization branches, the associated-principal
theorem supplies it directly. In the classical regular-ambient case,
the caller supplies minimality of each associated p, as follows from
the no-embedded-primes hypothesis. Regularity of a localized principal
quotient is never used in place of ambient regularity.

These criteria supply no reducedness assertion for the completion of
A/p. That separate input requires the actual quotient's Nagata property,
strict dimension drop, and the lower-dimensional analytic-unramifiedness
result. Finite-completion descent, the bounded Nagata-AU2 assembly, and
the separate F2/CN2 normalization theorem remain outside this module.
