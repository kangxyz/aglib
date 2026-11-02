# A comparison diagram for normalized point domination

Source: [Comparison.lean](Comparison.lean).

`NormalPointComparison q` is output data for a map `q : Q ⟶ S` of integral
schemes. It records a new base, a dominating model, the original maps
`beta`, `p`, `g`, the equation `g ≫ q = p ≫ beta`, a literal normalized
point chain for `beta`, and the stated normal, Noetherian, dimension,
properness, dominance and function-field properties.

Its curve condition is noncollapse under `g`.
For locally Noetherian normal `Q` of dimension at most two, `curveEmbedding`
derives the proper-image embedding `contractedCurves p ↪ contractedCurves q`.
A curve injection is not an independent field of the structure.

`comp` composes the original maps and chains. `curveEmbedding_comp` identifies
its curve map with the composite proper-image embedding;
`missing_curve_comp` propagates absence of a selected old curve.
`SelectedElimination` constructs these diagrams in its DVR-order induction.

Present consumers: [SelectedElimination](SelectedElimination.md).
