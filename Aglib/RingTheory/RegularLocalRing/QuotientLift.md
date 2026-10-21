# Regular locality from a regular principal quotient

`IsRegularLocalRing.of_quotient_span_singleton` proves that a Noetherian local
ring `R` is regular local when `x` is a nonzerodivisor and `R/(x)` is regular
local. The quotient regularity includes nontriviality, so no separate properness
premise or condition on the square of the maximal ideal is needed.

The proof lifts a minimal generating set of the quotient maximal ideal and
adjoins `x`. This bounds the number of generators of the original maximal ideal
by `dim(R/(x))+1`. The dimension inequality for a nonzerodivisor supplies the
reverse bound needed for regularity.

`IsRegularLocalRing.atPrime_of_quotient_span_singleton` applies the same result
at a prime containing `x`, assuming the global quotient is a regular ring.
It uses the actual mapped ideal in the prime localization and its canonical
quotient localization. The original scalar remains a nonzerodivisor there.

The first conclusion corresponds to [Stacks Lemma 10.106.7, tag
00NU](https://stacks.math.columbia.edu/tag/00NU), checked on 2026-10-22. The
proof is supplied in Lean; the source citation is not an imported premise.

The current consumer is regularity of the actual parameter charts of a
two-dimensional regular-local point blowup.
