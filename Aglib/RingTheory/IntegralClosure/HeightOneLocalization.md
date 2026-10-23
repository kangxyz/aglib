# Canonical height-one localization membership

This module applies the existing published height-one intersection proof to
the original canonical localization maps. Its hypotheses are exactly
`[CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]`.

`IsIntegrallyClosed.mem_range_of_mem_range_atPrime_height_one` and
`IsIntegrallyClosed.mem_range_iff_mem_range_atPrime_height_one` characterize
the image of `algebraMap R (FractionRing R)` by membership in the images of
`algebraMap (Localization.AtPrime P) (FractionRing R)` for all actual primes
`P` with `P.height = 1`. Mathlib's canonical scalar tower ensures that every
local representative maps into that same original fraction field. Clearing its
actual denominator supplies the premise of the existing
`IsIntegrallyClosed.mem_range_of_forall_height_one`.

`Ideal.mem_span_singleton_of_mem_map_atPrime_height_one` proves, for `a ≠ 0`,
that `b ∈ Ideal.span {a}` follows from

```lean
∀ (P : Ideal R) [P.IsPrime], P.height = 1 →
  algebraMap R (Localization.AtPrime P) b ∈
    (Ideal.span {a}).map (algebraMap R (Localization.AtPrime P))
```

`Ideal.mem_span_singleton_iff_mem_map_atPrime_height_one` includes the
immediate converse. The native
`IsLocalization.algebraMap_mem_map_algebraMap_iff` clears a denominator outside
each prime, and the existing `IsIntegrallyClosed.dvd_of_forall_height_one`
then gives the original divisibility. No nonzero condition on `b` is imposed.

The imported proof is the published chain
`HeightOneIntersection → HeightOneDivisibility → AssociatedHeight →
AssociatedPrincipal → HeightOne`. Those five unchanged leaves were restored
from Aglib revision `00972fe4b11ae9a512d064f40ed2c8d4f974d72a`; the chain ends
in native Mathlib dependencies. It proves the applicability of its
associated-prime height bound from the stated normal Noetherian domain
hypotheses. This bridge introduces no S2, factorization, intersection or
desired-membership premise and repeats none of the denominator-ideal proof.

The current consumer is `Surfaces.Resolution.VerticalCartier`, which must
check every height-one prime, including primes outside the divisor support.
The native basis is Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
