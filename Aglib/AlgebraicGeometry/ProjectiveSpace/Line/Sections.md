# Coordinate sections of the original projective line

Import `Aglib.AlgebraicGeometry.ProjectiveSpace.Line.Sections` and use
`AlgebraicGeometry.Scheme.ProjectiveLine.Sections`.

For every commutative ring `R`, `chartSection R i a` is the literal composite
`Spec.map (Polynomial.evalRingHom a) ≫ ProjectiveLine.chart R i`.
`infinity R` is `[0:1]` and `affinePoint R a` is `[1:a]` on the existing native
`ProjectiveLine.projectiveP1 R`. Their `*_over` theorems retain the original
structure triangle.

`section_coefficient`, `infinity_coefficient`, and `affinePoint_coefficient`
use the original `LinearChange.coefficientMap f` and `Spec.map f`; the affine
parameter becomes exactly `f a`. The original unipotent matrix is
`translationMatrix R t`, with rows `(1,0)` and `(t,1)` and inverse obtained by
negating `t`. Its multiplication and coefficient-change formulas are explicit.
`infinity_translation` and `affinePoint_translation` identify the actual
composite scheme morphisms: infinity is fixed and the parameter becomes `a+t`.

The proof uses only original graded polynomial maps. The native projective
space with one homogeneous coordinate is identified with the coefficient
spectrum using its sole coordinate chart and the polynomial ring in zero
variables. Maps from that auxiliary scheme are then identified with the
literal chart sections above by their original chart-ring maps on constants
and the coordinate ratio. No field, reducedness, nontriviality or density
hypothesis is used, and no second projective line is introduced.

The current consumer is the quotient section in
`ProjectiveBundle.RankTwoExtension`. The conormal and affine-complement
calculation for that bundle remains separate from these coordinate identities.
