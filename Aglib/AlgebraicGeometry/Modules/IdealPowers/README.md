# Ideal multiples of coefficient sheaves

`Basic` defines the actual ideal-generated coefficient as the image of scalar
evaluation from the coproduct indexed by the ideal. Its inclusion, quotient,
short exact sequence and maps under ideal inclusion are native categorical
maps. `idealPower` specializes to `I^n`, including `n = 0`; no flatness,
quasicoherence, properness or Noetherian hypothesis enters these definitions.

`Scalars` proves annihilation of the actual quotient by the defining ideal
and the zero quotient at degree zero. The cohomology tower and natural long
exact sequence are owned by `Cohomology/FormalFunctions/QuotientTower`.

`Multiplication` supplies genuine multiplication by homogeneous ideal elements
and its compatibility with ideal inclusions and lowering the action degree.
`QuasiCoherent` proves image and quotient quasicoherence on arbitrary schemes.
`Boundary` retains the original canonical map in the zero-ideal and degree-zero
identifications. `AffineEvaluation` identifies affine section images with the
native extended ideal times the section module, via the actual affine
coproduct cocone and categorical image comparison.

`AffineSections` keeps the existing structural-ring section action and identifies
actual affine sections of the ideal multiple with the native base-ring ideal
multiple. Its forward map is the original coefficient inclusion. The comparison
preserves ideal-inclusion transitions, homogeneous scalar multiplication, and
restriction maps on affine opens.

[ThickeningSections](ThickeningSections.lean) uses the original arbitrary affine
section base-change map to identify sections on the actual `Spec (A/J)` base
change with the ordinary ideal quotient. [Thickening](Thickening.lean) descends
the original pullback unit through the original coefficient cokernel and proves
the resulting map to actual pushforward is invertible on affine opens.
`idealThickeningBaseScalar` names the unchanged structural affine-base ring map. Its
quotient-projection normalization is the original geometric unit, with no
flatness assumption. [ThickeningTransitions](ThickeningTransitions.lean) retains
the actual quotient-ring-factor scheme maps, original coefficient unit arrows,
and naturality of this quotient/thickening comparison.
