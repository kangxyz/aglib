# Factoriality in every dimension

`IsRegularLocalRing.uniqueFactorizationMonoid_of_regularLocal` proves
native `UniqueFactorizationMonoid R` from only `CommRing R` and native
`IsRegularLocalRing R`. Domainness is derived internally from the existing
regular-local domain theorem. There is no dimension bound, excellence,
completion, characteristic, field, or factoriality premise.

`isPrincipal_of_height_eq_one` applies this result to an actual prime
ideal `p` satisfying `p.height = 1`. `heightOneIdealBasis` supplies a
`Basis PUnit R p` on that actual ideal module. The generator is nonzero
because a height-one prime in the resulting domain is nonzero, so the
basis uses regular multiplication by that generator.

The proof follows dimension induction in
[Stacks Project, Lemma 15.123.2, tag 0AG0](https://stacks.math.columbia.edu/tag/0AG0).
A first regular parameter `x` has regular domain quotient and is therefore
prime. Every prime localization of `R[1/x]` is a regular localization of
`R` at a nonmaximal prime, hence has smaller dimension. Induction makes
those local rings factorial. Each height-one prime on `R[1/x]` is then
locally principal, and the native local projectivity criterion makes its
ideal module projective.

[`PrincipalLocalization.lean`](PrincipalLocalization.lean) uses the
original finite ideal and its projective-dimension bound to obtain an
actual stable free complement. Rank-one cancellation supplies global
principality on `R[1/x]`. Native descent after inverting a prime element
then gives principality in `R`. Height-one primes containing `x` equal
`(x)` directly. The native height-one-prime criterion concludes unique
factorization. Thus the passage from local principality to global
principality uses a proved module argument.

All four lower suppliers are native algebraic owners:
[`PrimeLocalization.lean`](PrimeLocalization.lean),
[`PrincipalLocalization.lean`](PrincipalLocalization.lean),
[`StablyFreeBaseChange.lean`](../../Algebra/Category/ModuleCat/StablyFreeBaseChange.lean),
and [`StableRankOne.lean`](../../LinearAlgebra/FreeModule/StableRankOne.lean).
