# Relative forms on saturated regular-pair charts

[SheafBound](SheafBound.lean) works over commutative rings `Λ → R` and a
regular pair `x,y`. On the literal saturated `x`-chart, multiplication by
the exceptional coordinate sends every degree-`n` form into the image of
the original raw pullback. This image bound needs no domain or Noetherian
hypothesis.

The scaled section, sheaf and bidual maps in
[ScaledSections](ScaledSections.lean), [ScaledSheaf](ScaledSheaf.lean) and
[ScaledBidual](ScaledBidual.lean) use a domain `R`, its specified fraction
field with compatible `Λ`-scalars, the displayed regular pair and an
original map of degree-`n` forms to a line `L`.
[OnePoleChart](OnePoleChart.lean) tensors the pulled line with the actual
dual centre-ideal line and normalizes its coefficient by the original
denominator frame.

[OnePoleRawSquare](OnePoleRawSquare.lean),
[OnePoleSquare](OnePoleSquare.lean) and
[OnePoleTarget](OnePoleTarget.lean) retain evaluation, unit and target
comparisons for those same maps. The global two-chart consumer is
[PairIdeal](../PairIdeal/README.md).

Present consumers include [Relative forms on a two-generator ideal blowup](../PairIdeal/README.md).
