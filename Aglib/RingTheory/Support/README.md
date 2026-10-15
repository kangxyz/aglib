# Minimal support under localization

[Localization](Localization.lean), imported as `Aglib.RingTheory.Support.Localization`, exports `Module.localizedMinimalSupportEquiv` and the corresponding membership criteria. For a finite module localized at a prime, minimal support primes correspond to the original minimal support primes contained in that localization prime.

`Module.localized_minimalSupport_iff` retains a commutative ring `A`, finite `A`-module `M` and prime ideal `Q`, and accepts any ideal `p` of `Localization.AtPrime Q` without assuming `p.IsPrime`. It identifies minimality of `p` over the actual localized module's annihilator with minimality of `p.under A` over `Module.annihilator A M`. The lower `annihilator_le_localized_iff` still requires `p.IsPrime`.

The maps are canonical extension/contraction of actual prime ideals. Finite generation is retained for the annihilator/support detection; an annihilator base-change equality is not supplied as a separate premise. [Prime-filtration multiplicity](../PrimeFiltration/README.md) and [principal Euler associativity](../Multiplicity/PrincipalEuler/README.md) consume these comparisons.
