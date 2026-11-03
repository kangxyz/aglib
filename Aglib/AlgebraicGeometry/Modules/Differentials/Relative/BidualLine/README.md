# Bidual lines of top relative forms

[Model](Model.lean) works with an integral locally Noetherian regular
scheme `X` of dimension at most two, a domain `A`, a map `ρ : Λ → A`,
and a dominant `β : X → Spec A` with invertible original function-field
map. The composite to `Spec Λ` is locally of finite type.
A supplied `Fin n` basis of `Ω_(A/Λ)` fixes the top degree.

The bidual of the original degree-`n` relative-form sheaf is locally rank
one; `modelDifferentialLine` is that same sheaf as a line bundle.
[Affine](Affine.lean) and [ModelChart](ModelChart.lean) provide the affine
and chart versions with their regularity, finiteness and generic-rank
hypotheses.

[ModelCoefficient](ModelCoefficient.lean) uses the original ordered basis
coordinate to define the coefficient into this actual model line.
[ModelCoefficientFactorization](ModelCoefficientFactorization.lean)
identifies it with the raw pullback followed by bidual evaluation.
No rational-singularity or resolution hypothesis enters this family.

Present consumers include [Model](Model.md), [ModelChart](ModelChart.md).
