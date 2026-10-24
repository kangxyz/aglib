# The full exceptional fibre and its original coefficients

`exceptionalCurve A hd` is the full scheme cut out by the original exceptional
ideal m O_X in the ordinary maximal-ideal blowup. Its nilpotents are retained.
`exceptionalStructureMap` constructs its map to Spec(A/m) through the native
closed-immersion lift. The original quotient-spectrum inclusion, exceptional
inclusion and blowdown satisfy `exceptionalStructureMap_triangle`; the same
square is proved Cartesian. Properness and surjectivity come from actual base
change of the ordinary blowdown.

The normality and H1 statements assume a commutative Noetherian Nagata normal
local domain A of dimension two and the existing honest
`NormalModificationH1Vanishing A` predicate. Ordinary normalization is supplied
by [Normality](Normality.lean), and normalized ideal-power H1 by
[IdealPowers](IdealPowers.lean).

The proved normalization isomorphism makes the original structural unit an
isomorphism. Its positive-power projection square proves
`ordinaryPositivePowerNormalization_isIso` for the same
`idealPowerNormalizationUnit`. The original affine direct-image cohomology
comparison then derives `ordinaryPositiveIdealPower_H1`, with the original
A-action retained.

In degree one this gives H1(I)=0 for the original kernel ideal I. The native
short exact ideal sequence therefore makes the actual restriction map
Gamma(X,O_X) -> Gamma(E,O_E) surjective. The base ring's original coefficient
bijection supplies all sections of the source. The constructed residue-field
coefficient map is injective because E is nonempty, and its original quotient
values show surjectivity. Thus `exceptionalCoefficients_bijective` and
`exceptionalCoefficientsEquiv` identify H0(E,O_E) with the original A/m.
The displayed isomorphism is this actual structural coefficient map.

These conclusions apply to regular rational local surfaces as well. No
Gorensteinness, degree-two statement, tangent presentation, chosen resolution,
coefficient-field section or desired H0-isomorphism is assumed. Higher
exceptional twists, the matched projective O(1) comparison and closed-stalk
geometry remain subsequent consumers. Later canonical-generation arguments
that seek degree two must retain singularity of A or the genuine degree-at-least-two
input; they are not conclusions of this module.

The mathematical source for the exceptional section sequence is
[Stacks 54.9.5, 0B63](https://stacks.math.columbia.edu/tag/0B63).
