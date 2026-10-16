# Support, localization and annihilating powers

[Localization](Localization.lean), imported as `Aglib.RingTheory.Support.Localization`, exports `Module.localizedMinimalSupportEquiv` and the corresponding membership criteria. For a finite module localized at a prime, minimal support primes correspond to the original minimal support primes contained in that localization prime.

`Module.localized_minimalSupport_iff` retains a commutative ring `A`, finite `A`-module `M` and prime ideal `Q`, and accepts any ideal `p` of `Localization.AtPrime Q` without assuming `p.IsPrime`. It identifies minimality of `p` over the actual localized module's annihilator with minimality of `p.under A` over `Module.annihilator A M`. The lower `annihilator_le_localized_iff` still requires `p.IsPrime`.

The maps are canonical extension/contraction of actual prime ideals. Finite generation is retained for the annihilator/support detection; an annihilator base-change equality is not supplied as a separate premise. [Prime-filtration multiplicity](../PrimeFiltration/README.md) and [principal Euler associativity](../Multiplicity/PrincipalEuler/README.md) consume these comparisons.

[Powers](Powers.lean), imported as `Aglib.RingTheory.Support.Powers`, proves
`Module.exists_pos_pow_le_annihilator_of_support_subset`: for a finite
module over any commutative ring, support contained in `V(I)` gives an
actual positive power `I ^ n ≤ Module.annihilator R M` when `I` is finitely
generated. No Noetherian or nontrivial-ring hypothesis is imposed, and
ring and module carrier universes are independent. The converse support
statement requires neither module finiteness nor ideal finite generation.
The corresponding native support/power equivalence is public.

The source passed through the shared single-leaf guard with receipt
`1792112291756043000-81297` in 1.8 seconds at the default budget. The
independent mixed-universe `SupportPowersConsumer.lean` passed with receipt
`1792112370963630000-82492`; all three inspected declarations use only the
three standard axioms. Actual scheme support-power descent consumes this
lower result without an ideal-adic filtration or prime-filtration premise.
