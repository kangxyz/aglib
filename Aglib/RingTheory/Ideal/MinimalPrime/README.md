# Minimal-prime contraction and flat base change

[FlatBaseChange](FlatBaseChange.lean), imported as `Aglib.RingTheory.Ideal.MinimalPrime.FlatBaseChange`, gives `Ideal.minimalPrime_map_under` and the corresponding extension/contraction criterion under actual flat scalar extension. The ideal and algebra maps remain the original ones.

[GoingDown](GoingDown.lean) contracts a minimal prime over an extended ideal when `Algebra.HasGoingDown` is supplied. Its normal-base integral-domain variant retains the normality, integrality and faithful/domain hypotheses used to obtain going down.

These results partition actual minimal support primes for localization/flat extension. [Support](../../Support/README.md), prime filtrations and principal Euler associativity are consumers. The conditional going-down interface is distinct from a claim that every extension has going down.
