# Algebra of saturated blowup charts

[PowerNode](PowerNode/README.md) computes the literal saturated Rees charts and
localization transitions for UV = pi^(m+2) at the ideal (U,V,pi). Its reusable
algebra lives below schemes and retains the original domain, UFD and nonzero
scalar hypotheses. The canonical generated subalgebra belongs to
[Localization/Away/SaturatedChart](../Localization/Away/SaturatedChart.lean).

Global blowup data and the separately stated existence, atlas, properness and
flat-base-change families belong to
[AlgebraicGeometry/Blowup](../../AlgebraicGeometry/Blowup/README.md).

[RegularPair](RegularPair.md) compares the quotient by `a X - b` for an actual
regular pair with the original saturated chart, and computes its coefficient
fibre. Its [reciprocal comparison](RegularPair/Reciprocal.md) retains both
original ratio coordinates and their Laurent transition. The regular-pair
supplier for two-dimensional regular local rings is used by the actual
[regular-point blowup](../../AlgebraicGeometry/Blowup/RegularPoint.md).

[WeakTransform](WeakTransform.md) divides an ideal `J` by an exceptional power
in the literal `saturatedChart A I a`. The transform is the colon of the
extended ideal by the image of `a ^ r`. For `a ∈ I` and `J ≤ I ^ r`, the
exceptional power times this transform is exactly the original extended `J`.
The construction works over every commutative ring. Identifying its extension
with a target colon requires regularity of the exceptional parameter's image.

[Colength](Colength.md) constructs the actual order of an ideal in a regular
parameter pair from the stated power containments. Under its Noetherian,
maximal-parameter-ideal and finite-colength hypotheses, the actual-order weak
transform has Artinian chart quotient and strictly smaller local colengths.
`weakTransform_local_colength_toNat_lt` retains the actual localized quotient,
positive order and both ideal-power bounds. The
[finite point-blowup consumer](../../AlgebraicGeometry/Surfaces/Resolution/README.md)
uses these individual strict inequalities in a multiset termination argument.
