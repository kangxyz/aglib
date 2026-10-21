# Integral closure away from a prime element

`PrimeAway.lean` proves that a domain `R` is integrally closed when its
localization away from a prime element `p` is integrally closed. The public
criterion is `IsIntegrallyClosed.of_isLocalizationAway_prime S hp`, where
`[IsLocalization.Away p S]` identifies the actual localization and
`hp : Prime p`. There is no Noetherian, local, dimension, or finiteness assumption.

The cancellation step `Prime.dvd_of_integral_mul` works in a faithful domain
extension `R → S`. If `z` is integral over `R` and `a = p*z` in `S`, then
`p ∣ a` in `R`. In the actual integral closure of `R` in `S`, native prime
lying-over gives a prime above `(p)`. Membership of `a` in that prime contracts
to membership in `(p)`. The proof uses
`Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain` and its stated kernel
condition; it needs no finiteness of the integral closure.

`Prime.exists_algebraMap_eq_of_integral_primePow_denominator` applies this
cancellation repeatedly to an integral element represented as `a / p^n`.
The actual localization surjectivity theorem supplies that representation in
`IsIntegrallyClosedIn.of_isLocalizationAway_prime`. Transitivity with the
integral closedness of `S` yields the final absolute criterion.

The current consumer is
`AlgebraicGeometry/EllipticCurve/Weierstrass/Normality.lean`, where `p` is the
image of a DVR uniformizer in either literal affine chart ring. This file
does not infer normality from generic normality alone: the primality of `p`
is a required, explicit hypothesis.
