# The curve DVR and its finite natural order

Source: [CurveOrder.lean](CurveOrder.lean).

For a proper dominant birational `f : X ⟶ Y` with integral source and target,
normal locally Noetherian `Y`, and `topologicalKrullDim X ≤ 2`,
`contractedCurvePoint` associates to a contracted curve its original generic
point as a `CodimensionOnePoint X`. Its actual stalk has dimension one.

For integral locally Noetherian `X` with integrally closed stalks, that stalk
is the native DVR. `CodimensionOnePoint.finiteOrder` is the natural value of
its additive valuation. `addVal_ne_top_of_ne_zero` gives finiteness for
nonzero elements, `finiteOrder_pos` gives positivity for nonzero nonunits,
and `finiteOrder_mul` gives additivity on nonzero products.

`finiteOrder_lt_of_factor` uses `a = a' * d`, `a ≠ 0` and nonunit `d` to prove
strict decrease. `finiteOrder_stalkMap_lt_of_factor` gives the same result
after the original local stalk map. The geometric exceptional factor and
retained fraction are supplied separately by `ExceptionalGenerator` and
`SelectedStep`.

Present consumers: [CurveOrderTransport](CurveOrderTransport.md).
