# Ring Picard groups across square-zero extensions

[SquareZero](SquareZero.lean) proves actual invertible-module lifting over a
surjective homomorphism `f : R ->+* S` of arbitrary commutative rings with
`(ker f)^2 = 0`. Finite-projective object lifting first lifts the module and
a tensor inverse; prescribed isomorphism lifting then recovers an actual
tensor equivalence with `R`.

`CommRing.Pic.mapRingHom_bijective_of_square_zero` proves bijectivity of
Mathlib's original `mapRingHom f`, and `squareZeroEquiv_apply` retains that
forward map definitionally. The source rings need not be Noetherian or
local, and the ring extension need not be flat or split.

The [affine line-bundle application](../../AlgebraicGeometry/Modules/Invertible/SquareZero/README.md)
uses the actual affine Picard and associated-sheaf comparisons. Global
scheme Picard groups are treated separately; affine invariance does not
assert global Picard injectivity across a thickening.
