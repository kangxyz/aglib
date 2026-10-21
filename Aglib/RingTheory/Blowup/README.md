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
