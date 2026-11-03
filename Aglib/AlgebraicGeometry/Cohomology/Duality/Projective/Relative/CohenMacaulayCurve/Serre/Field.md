# Curve cohomology with original field constants

Source: [Field.lean](Field.lean).

`cmCurveSerreCohomologyFieldLinearEquiv` specializes the original constants-action
module isomorphism to `Over.mk (j ≫ toSpec k ι)`. Its source is the existing
`cmCurveSerreCohomology`, and its target is the existing field-scheme
`moduleCohomology`. The underlying additive sheaf-cohomology group is unchanged.

The finrank theorem records the resulting equality of dimensions for any module
sheaf and natural degree. No finite-dimensionality, closed-embedding, or
Cohen--Macaulay hypothesis is needed for this carrier comparison. It neither
identifies the coefficient line with the ground field nor supplies a canonical-sheaf
base-change theorem.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/CohenMacaulayCurve/AnticanonicalHilbert/ScalarExtension](../AnticanonicalHilbert/ScalarExtension.md).
