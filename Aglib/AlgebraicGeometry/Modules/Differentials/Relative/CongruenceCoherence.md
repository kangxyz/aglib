# Coherence of original differential congruences

Source: [CongruenceCoherence.lean](CongruenceCoherence.lean).

The two theorems prove transitivity and reversal of the existing
relativeDifferentialCongrIso, whose constructor uses the original universal
derivations. Equality induction invokes its already proved reflexivity.
No comparison is replaced by eqToIso and no new congruence constructor is made.
All schemes and structural morphisms remain arbitrary; no finiteness,
quasicoherence, smoothness, or field premise is added.

Direct consumers: [AlgebraicGeometry/Modules/Differentials/Relative/ExteriorCoefficientCoherence](ExteriorCoefficientCoherence.md).
