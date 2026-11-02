# DVR-order transport through the original stalk map

Source: [CurveOrderTransport.lean](CurveOrderTransport.lean).

`IsDiscreteValuationRing.addVal_ringEquiv` proves equality of the native
normalized additive valuations under any ring equivalence of DVR domains.

`CodimensionOnePoint.finiteOrder_stalkMap` specializes this to a scheme map
`f : X ⟶ Y` between integral locally Noetherian schemes with integrally
closed stalks. Its source point is codimension one, its literal image
`f x` has stalk dimension one, and `f.stalkMap x` is an isomorphism.
The theorem identifies the two finite orders through that very map,
without an additional valuation-compatibility premise.

This preserves the selected curve's order across a surviving common-model
projection in exceptional division.

Present consumers: [FractionTransform](FractionTransform.md).
