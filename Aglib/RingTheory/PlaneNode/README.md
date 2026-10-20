# The literal plane-node algebra

[Basic](Basic.lean), in `PlaneNode`, owns the actual `AdjoinRoot` presentation
`Ring c` of R[U,V]/(UV-c), its elements `U,V`, their relation, the universal
algebra map and its uniqueness. It also gives the original branch-coordinate
unit scaling. These constructions work over arbitrary commutative rings.

[CoordinateTransport](CoordinateTransport.lean) gives literal tensor coefficient
base change, the original coefficient map and its etale property for etale
coefficient extension. It retains the congruence and unit-scaled equivalences
with their actual coordinate formulas. It has no scheme dependency.

The [power-node saturated charts](../Blowup/PowerNode/README.md) reuse this ring.
The actual scheme pullback comparison, with both projections identified, lives
in [Curves/Nodal/CoordinateTransport](../../AlgebraicGeometry/Curves/Nodal/CoordinateTransport.lean),
under `Scheme.PowerNode`.
