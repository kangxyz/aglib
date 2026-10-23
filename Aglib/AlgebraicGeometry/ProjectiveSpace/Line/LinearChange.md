# Linear coordinate changes on the original projective line

Import `Aglib.AlgebraicGeometry.ProjectiveSpace.Line.LinearChange` and use
`AlgebraicGeometry.Scheme.ProjectiveLine.LinearChange`.

For any commutative ring `R`, `matrixMap R M` is the morphism on the existing
`Scheme.ProjectiveLine.projectiveP1 R` induced by the original row forms of an
invertible two-by-two matrix `M`. `matrixIso` and `matrixOverIso` retain that
forward map and its original structure triangle. No reducedness, nontriviality
or field hypothesis is required.

The coordinate pullback convention is explicit:
`matrixMap R M ≫ matrixMap R N = matrixMap R (N * M)`.
The proof uses inverse graded substitutions to establish the irrelevant-ideal
condition on the whole original Proj. It does not require a matrix to preserve
an individual affine chart.

For the original ring homomorphism `f : R →+* S`, `coefficientMap f` is the
native homogeneous coefficient morphism on the same two-coordinate Proj.
`coefficientMap_matrixMap` identifies its composites with the original matrix
map and the matrix obtained by applying `f` to every coefficient.
`coefficientMap_isPullback` proves that it and the original structure maps form
the cartesian square over `Spec.map f`. The proof transports the existing
polynomial projective-space base-change square through the actual finite
coordinate reindexing isomorphisms; it does not define another projective line.

`ProjectiveSpace.Line.TwoPoints` keeps its original field-facing declaration
names as adapters to this single implementation. The ring-level coefficient
and matrix interfaces are also used by the rank-two extension bundle route.
