# Pointed projective maps of native Weierstrass variable changes

For any commutative ring `R`, a literal `W : WeierstrassCurve R`, and an actual
native admissible change `C = (u, r, s, t)` with its supplied unit `u : Rˣ`,
`WeierstrassCurve.VariableChange.projectiveOverIso W C` is an actual
isomorphism from `curveOver (C • W)` to the same original `curveOver W`.
The forward homogeneous coordinate pullback is

\[
 X\longmapsto u^2X+rZ,\qquad
 Y\longmapsto u^3Y+s u^2X+tZ,\qquad
 Z\longmapsto Z.
\]

Constants are fixed. The substitution sends the original cubic to `u⁶` times
the transformed cubic. Its polynomial substitutions satisfy the exact native
group law, so the actual inverse native change supplies the inverse polynomial,
quotient, graded, and Proj maps. All grading statements use the original
ordinary total-degree grading.

`projectiveHomogeneous_x`, `projectiveHomogeneous_y`, and
`projectiveHomogeneous_z` expose the literal forward maps on the existing
homogeneous cubic quotient. `projectiveIso_over` retains the original
base-ring structural map. `projectiveIso_infinity` retains the actual infinity
section as a morphism over `Spec R`.

The infinity proof uses the common chart `D(Y · L)`, where
`L = u³Y + s u²X + tZ`. The original infinity evaluation sends `Y` to `1`
and `L` to the actual unit `u³`. The generic homogeneous-scaling identity and
the native chart transitions therefore give equality of the section morphisms,
including over nonreduced rings. The field-valued
`projectiveIso_infinityPoint` remains a specialization for the existing
field-only point interface.

The construction works in every characteristic, including zero rings, without
a domain, nonvanishing-discriminant, smoothness or regularity hypothesis.
Inversion is used only in the native unit group and in the actual chart
localizations. It realizes the supplied native change on the literal cubic.

`IntegralModel` uses this provider for its denominator change, its native DVR
minimum, and the pointed projective comparison over the original DVR for the
same descended change. Presenting an abstract pointed genus-one curve and
selecting a native minimum remain with their respective producers and retain
their own hypotheses.
