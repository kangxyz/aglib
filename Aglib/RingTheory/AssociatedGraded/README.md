# Associated graded rings and modules

[Basic](Basic.lean) defines `Ideal.associatedGraded` as the quotient of the
native `reesAlgebra I` by the extension of the original ideal from degree
zero. Its defining ideal consists of Rees polynomials whose degree-`n`
coefficient lies in `I ^ (n + 1)`. The quotient has the native grading and is
Noetherian when the original ring is Noetherian.

[Components](Components.lean) identifies the degree-`n` component with
`I ^ n / I ^ (n + 1)` through the original homogeneous monomial map.
[Multiplication](Multiplication.lean) records multiplication of these
representatives and identifies the degree-zero structural algebra map.
[NativeRing](NativeRing.lean) exposes the original quotient ring instance.

[DegreeZeroGeneration](DegreeZeroGeneration.lean) proves finiteness of an
external graded module from finite degree zero, compatible base scalars,
and explicit homogeneous generation. [BoundedGeneration](BoundedGeneration.lean)
extracts a degree bound from finite generation of the actual direct sum.
[TensorPositiveGeneration](TensorPositiveGeneration.lean) and
[TensorComponentGeneration](TensorComponentGeneration.lean) supply the
corresponding bounded positive-degree span over the actual tensor coefficient
ring. [ExternalScalars](ExternalScalars.lean) retains the coordinate and base
scalar actions used in that tensor construction.

[TensorRing](TensorRing.lean) exposes the native tensor ring with its specified
associated-graded quotient factor.
[CoordinateModuleBijective](CoordinateModuleBijective.lean) specializes the
coordinate pushout comparison to this quotient, including its direct-sum
variant. These algebraic suppliers feed the geometric graded realizations in
[Grothendieck existence](../../AlgebraicGeometry/Cohomology/GrothendieckExistence/README.md).

[Cotangent/Graded](Cotangent/Graded.md) bundles the original polynomial map
to the native Rees-quotient associated graded ring over the actual coefficient
quotient. It preserves the existing homogeneous carriers and grading.
Spanning by the chosen ideal generators or their cotangent classes yields
surjectivity. This feeds the full quadratic-kernel presentation; it does
not supply a Hilbert function from surface geometry.
