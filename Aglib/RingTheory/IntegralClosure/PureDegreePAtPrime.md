# Original normalization at a height-one prime

Let A be a normal domain with its original fraction field K, and let L/K be
a finite purely inseparable extension of prime degree p in characteristic p.
All normalizations are literal integral closures in this original L.

`pow_mem_base_of_pure_degree` derives b^p∈A for every b in
B=integralClosure A L. The field exponent theorem puts b^p in K and original
normality descends its integrality to A. For a prime Q over q,

```text
b ∈ Q  iff  b^p ∈ Q  iff  a_b ∈ q, where b^p = a_b ∈ A.
```

Consequently `existsUnique_prime_of_pure_degree` gives the unique prime Q
above q, using integral lying over through the original injective map.

For D=A_q and C=integralClosure D L, the existing scalar-extension inclusion
B→C preserves every ambient element of L and makes C the localization at
the image of A outside q. If b is outside Q, then b divides b^p and b^p is
in that image. Thus the same actual inclusion makes C the localization
B_Q, as proved by `scalarExtension_isLocalization_atPrime_of_pure_degree`.

At height one in a normal Noetherian A,
`isDiscreteValuationRing_of_height_one` derives the DVR structure on D.
`exists_presentation_at_height_one_of_pure_degree` transports the original
Module.Finite A B through the actual localized-module map to obtain
Module.Finite D C. The original K remains the fraction field of D.

The actual DVR normalization presentation theorem then supplies
`h : IsAdjoinRootMonic C (X^p-C a)`, its original root, pth-power equation
and aeval map. Its finite-DVR calculation derives e f=p and the two actual
Nakayama-generated power-basis presentations. No monogenicity, desired
basis, defectlessness, residue-field section, separable residue extension,
perfect field, finite p-rank, or differential smoothness is assumed.
Noetherianity of C as a ring is not substituted for its module finiteness.

The current differential consumer is the actual height-one denominator
proof for the global integral-normalization trace.
