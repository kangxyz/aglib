# Generic power comparison for regular curves

`Zero.lean` and `Successor.lean` prove that the actual divisor tensor-power map
agrees with the canonical generic trivialization. The parent `GenericPower.lean`
applies the result to the genuine divisor/function pair `(D, f)` satisfying
`principal(f) = n • D`.

The original assumptions remain explicit: an integral Noetherian scheme, DVR
stalks at all closed points, and topological dimension at most one where the
actual divisor line bundle is required. There is no properness, chosen
arithmetic model, representability or cohomology-comparison premise in this
power calculation. Level zero uses the actual free-module unit and equality
transport; the successor uses the actual tensor/pullback comparisons.

The specified pair trivialization is the composite of `divisorPowerIso`, the
actual `eqToIso` for `principal(f) = n • D`, and `principalTrivialization f`.
Under the generic isomorphism it is multiplication by the positive field unit
`f`, obtained by `Units.map` along the inverse `ΓSpecIso`. A compatible frame is
an isomorphism from the line bundle to the unit; its scalar has nth power `f`.
The inverse section coordinate satisfies `f * s^n = 1`.

The generic suppliers are the native `Invertible.PowerPullback`,
`Invertible.TrivializedPower`, `Invertible.UnitPower` and `Invertible.Power`
coherence APIs. The divisor/function quotient and its comparison with actual
power-pair classes are in the sibling `KummerPairs`, `KummerExactness` and
`TrivializedPower` files. Their equivalences that require roots of global units
retain the original positive-level and global-constant hypotheses.

Source identity: the exact ordinary R5 Picard sources at revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`; each leaf records its source SHA-256.
Fresh build receipts and declaration correspondence are reported separately.
