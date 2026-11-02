# Birational maps on adapted affine charts

Source: [AdaptedCharts.lean](AdaptedCharts.lean).

Let `f : X ⟶ Y` be dominant between integral schemes, and let `U ⊆ X` and
`V ⊆ Y` be nonempty opens with `hUV : U ≤ f ⁻¹ᵁ V`.
`appLE_germToFunctionField` identifies the literal section map `f.appLE V U hUV`
with `functionFieldMap f` after the two generic germs.
`appLE_injective` proves that section map injective.

If `V` is affine and the original function-field map is an isomorphism,
`appLE_isAlgebraic` proves algebraicity for the scalar action induced by that
same section map: a source section satisfies a nonzero linear polynomial
obtained from its fraction expression in target sections.

For locally finite-type `f`, affine `U,V`, Nagata `Γ(Y,V)` and
`topologicalKrullDim Y ≤ 2`, `adaptedChart_nagata_and_dimension` proves that
`Γ(X,U)` is Nagata of dimension at most two. If every nonempty affine chart
of `Y` is Nagata, `dimension_le_two_of_birational` gives the same dimension
bound on `X`. The argument uses
`IsNagataRing.of_finiteType_isAlgebraic_and_dimLE_two` with its dimension
restriction, rather than an arbitrary-dimensional finite-type stability claim.

This is the adapted-chart finiteness step for
[Stacks tag 0BBT](https://stacks.math.columbia.edu/tag/0BBT).

Present consumers: [AffineBaseCharts](AffineBaseCharts.md), [FiniteNormalization](FiniteNormalization.md), [Resolution/IntermediateFieldModel](../../Resolution/IntermediateFieldModel.md).
