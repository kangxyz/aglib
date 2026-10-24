# Finite normalization of reduced Nagata rings

`integralClosure.finite_of_isNagataRing R hR Q` proves finiteness of the
literal `integralClosure R Q` over R when R is reduced and Nagata and Q
is its supplied total quotient ring. Noetherianity is derived from the
Nagata predicate. Locality, completeness, dimension, and a domain
structure are not hypotheses.

The theorem retains the original `Algebra R Q` and `IsFractionRing R Q`.
The Nagata predicate has auxiliary test universe zero; Q may lie in an
independent universe because the tested component fields are the canonical
fraction fields of the quotients of R.

The actual maps in [CompleteCurve](../IntegralClosure/CompleteCurve.lean)
apply without a dimension bound. A nonzerodivisor of R remains nonzero
in each minimal-prime quotient R/p, so the original quotient map extends
to `toMinimalPrimeFraction R Q p hp`. Mapping integral equations restricts
it to `toMinimalPrimeNormalization R Q p hp`, retaining the original
R-coefficient action. Their product `toMinimalPrimeNormalizations R Q`
is injective when R is reduced: the denominator calculation reduces its
kernel to the intersection of the minimal primes, and reducedness kills
the resulting nilpotent numerator.

For each minimal prime p, the Nagata clause makes R/p Japanese. Applying
it to the degree-one extension of its canonical fraction field gives
finiteness of its literal normalization over R/p. The finite quotient
R→R/p and scalar transitivity give finiteness over R. Noetherianity makes
the set of minimal primes finite, so their product normalization is a
finite R-module. The injective R-linear map then proves finiteness of
the original normalization. Q is used as supplied throughout.

The current concrete consumer is
[CompleteLocalSurface](CompleteLocalSurface.lean), which derives the
Nagata predicate for complete Noetherian local rings of dimension at
most two and applies this theorem to reduced rings. This generic owner
has no dependency on that complete-surface result. Its conclusion is
module finiteness; it does not assert finite length of the normalization
or its quotient.
