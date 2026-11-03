# Proper normalized point steps over the original base

Source: [PointStep.lean](PointStep.lean).

Let `b : X ⟶ P` be proper and dominant with integral `X,P`, Noetherian `P`,
invertible original function-field map, `topologicalKrullDim P ≤ 2`,
and Nagata nonempty affine charts of `P`.
For a closed nongeneric `x : X`,
`normalizedPointBlowupMap_isProper_over_base` proves the literal
`normalizedPointBlowupMap X x hx hne` proper.
`normalizedPointBlowup_isNoetherian_over_base` and
`normalizedPointBlowup_dimension_over_base` give its source Noetherianity
and dimension at most two.

The ordinary point blowup is integral and proper; its accumulated map to `P`
is birational. `FiniteNormalization` makes its original generic normalization
finite. Integrality, normality, dominance and the function-field isomorphism
are supplied by `NormalizedPointBlowupChain`.
The centre need not be singular, and `X` need not be regular.

Present consumers: [SelectedElimination](SelectedElimination.md).
