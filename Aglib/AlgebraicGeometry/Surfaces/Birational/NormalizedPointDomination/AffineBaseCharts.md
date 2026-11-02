# Affine charts of a Nagata domain surface spectrum

Source: [AffineBaseCharts.lean](AffineBaseCharts.lean).

For a commutative domain `A`, `IsNagataRing.{u,0} A` and
`ringKrullDim A ≤ 2`, `affineCharts_isNagata_of_nagata` proves Nagata for
every nonempty affine chart of `Spec A`. Normality and locality of
`A` are not needed.

The proof uses the native `ΓSpecIso`, transport through its ring equivalence,
and the identity-map instance of `AdaptedCharts`. This supplies the chart
hypotheses of `AffineBase`, and the chart and dimension arguments for
finite-type birational local models over the same spectrum.

Present consumers: [AffineBase](AffineBase.md), [Birational/StalkNagata](../StalkNagata.md), [Resolution/NormalizedPointBlowupChain/LocalStages](../../Resolution/NormalizedPointBlowupChain/LocalStages.md).
