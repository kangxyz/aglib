# Binary-form multiplication

This family constructs the actual coefficient morphism from the native finite
over-product `(P¹_R)^n` to `ProjectiveSpace R (ULift (Fin (n + 1)))`. Coordinate
`k` is the coefficient of `T^(n-k) U^k` in
`∏ i, (x i * T + y i * U)`. The construction retains the original projective
factors and their structural maps.

| Source group | Interface |
| --- | --- |
| [Basic](Basic.lean), [Algebra](Algebra.lean), [CoefficientPolynomial](CoefficientPolynomial.lean) | Original product, coefficient normalization and polynomial formulas. |
| [Map](Map.lean), [LocalCoordinates](LocalCoordinates.lean) | The actual projective morphism and its coordinate formulas. |
| [BaseChangeSource](BaseChangeSource.lean), [CoordinateHomExt](CoordinateHomExt.lean), [BaseChangeCoordinates](BaseChangeCoordinates.lean), [BaseChangeRefined](BaseChangeRefined.lean), [BaseChange](BaseChange.lean) | Original source base change, chart comparisons and the actual cartesian coefficient-map square. |
| [PointCoordinates](PointCoordinates.lean), [PointEvaluation](PointEvaluation.lean), [PointImage](PointImage.lean), [ProductPoints](ProductPoints.lean) | Original point coordinates, evaluations and image data. |
| [FieldAlgebra](FieldAlgebra.lean), [FieldPoints](FieldPoints.lean), [Fibers](Fibers.lean) | Factor and fibre inputs for the global geometric result. |
| [Finite](Finite.lean), [Surjective](Surjective.lean) | The actual morphism is finite and surjective. |

Finiteness and surjectivity hold for every commutative ring `R` and every
`n`, including `n = 0`. No factor of `n!` needs to be invertible; there is no
reducedness, characteristic, or flatness restriction. For any commutative rings
`R` and `S` in the same universe and any `σ : R →+* S`, the actual square
commutes:

```lean
multiplication S n ≫ ProjectiveSpace.map σ (ULift (Fin (n + 1))) =
  sourceBaseChangeMap σ n ≫ multiplication R n
```

The square is an `IsPullback`. `multiplicationBaseChangeIso` retains its
original maps: its first projection is `sourceBaseChangeMap σ n`, and its
second is `multiplication S n`. This holds for every `n`, including zero, over
arbitrary rings and ring maps; the local-coordinate proof retains the original
ratio and coefficient formulas, including over nonreduced rings.

This is a supplier for projective-space and future cohomological arguments;
it is not itself a proper-base-change result.
