# Packet 1 source correspondence

Native source: `Aglib/AlgebraicGeometry/RationalPoint/ClosedLift.lean`.

Frozen source: `R5Lab.Aglib.AlgebraicGeometry.RationalPoints.ClosedLift`, R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.

SHA-256: `1ab6e79c642de167b7ba14424d6e713dbcf62d8fa8204f22a0e2519ef75a7449`. Selected lines: `[[28, 110]]`.

The closed-immersion lift is over the same field and preserves the actual structural triangle. Rational-point equality retains both section equations. Pullback rationality retains the prescribed underlying point and both literal projections; it assumes no global injectivity.

| Original declaration | Native declaration | Source line |
| --- | --- | --- |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.closedImmersion_fieldPoint_lift` | `AlgebraicGeometry.Scheme.RationalPoint.closedImmersion_fieldPoint_lift` | 28 |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.closedImmersion_rationalPoint_lift` | `AlgebraicGeometry.Scheme.RationalPoint.closedImmersion_rationalPoint_lift` | 45 |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.rationalPoint_eq_of_apply_eq` | `AlgebraicGeometry.Scheme.RationalPoint.rationalPoint_eq_of_apply_eq` | 54 |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.pullback_rationalPoint_at` | `AlgebraicGeometry.Scheme.RationalPoint.pullback_rationalPoint_at` | 70 |

Frozen source: `R5Lab.Aglib.AlgebraicGeometry.RationalPoints.SectionExt`, R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.

SHA-256: `0830a656453da3422a6cbcef4c07fc88f029c7fd0f782fd6af9ff2fd79605e37`. Selected lines: `[[26, 55]]`.

rationalSection_ext delegates to the same rationalPoint_eq_of_apply_eq helper after identifying default with IsLocalRing.closedPoint k by uniqueness of the point of Spec k. Both section triangles remain explicit; no algebraic-closure premise is introduced.

| Original declaration | Native declaration | Source line |
| --- | --- | --- |
| `R5Lab.AlgebraicGeometry.Curves.LocalModels.ActualBranchSections.rationalSection_ext` | `AlgebraicGeometry.Scheme.RationalPoint.rationalSection_ext` | 26 |

Compilation evidence and actual provider identities are returned in the assigned scratch manifest. Compilation does not provide a theorem-family witness or mathematical-adoption status.
