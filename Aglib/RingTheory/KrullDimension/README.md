# Prime heights and local dimension

[IntegralExtension](IntegralExtension.lean) gives `PrimeSpectrum.primeSpectrum_height_comap` and `Ideal.height_eq_height_under` for integral extensions with supplied going down. The normal-base variant retains its domain and faithful integral-extension conditions. No finite-dimensionality premise is imposed.

[Polynomial](Polynomial.lean) gives the height formula at maximal polynomial primes, localized dimension bounds and regular-local polynomial rings over arbitrary fields with finitely many variables. Maximal residue extensions need not be separable. These native `MvPolynomial` results feed actual [polynomial scheme stalks](../../AlgebraicGeometry/Stalk/README.md) and smooth dimension/regularity.

[HeightOnePrime](HeightOnePrime.lean) gives `IsLocalRing.exists_heightOne_prime_not_mem`: in a Noetherian local domain of dimension greater than one, a height-one prime avoids the specified nonzero nonunit. [PrincipalOpen](PrincipalOpen.lean) gives `IsLocalRing.ringKrullDim_le_two_of_principal_open_height_le_one`: in a Noetherian local domain, if a nonzero `t` has every prime avoiding `t` of height at most one, the ring has Krull dimension at most two.

Focused imports are the four `Aglib.RingTheory.KrullDimension` leaves. Height/dimension bounds retain their hypotheses and do not assert regularity or normality merely from a numerical bound.
