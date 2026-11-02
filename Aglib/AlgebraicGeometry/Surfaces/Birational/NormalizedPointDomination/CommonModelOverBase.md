# Common-model finiteness over the original base

Source: [CommonModelOverBase.lean](CommonModelOverBase.lean).

Use the common-open data and maps of `CommonModel`, with integral `S,P` and
Noetherian `P`. Assume `f : X ⟶ S` is dominant and birational, and retain a
proper dominant birational `b : S ⟶ P`. The dimension of `P` is at most two,
and every nonempty affine chart of `P` is Nagata.

`normalization_isFinite_over_base` applies `FiniteNormalization` to the
original graph projection followed by `f ≫ b`.
`projections_isProper_over_base` and `pair_isFinite_over_base` give properness
of both existing projections and finiteness of their pair into the original
fibre product. `model_isNoetherian_over_base` and `model_dimension_over_base`
give Noetherianity and dimension at most two.

The common open remains input here; `NormalCommonModel` constructs it from
the original isomorphism loci and uses these finiteness results.

Present consumers: [NormalCommonModel](NormalCommonModel.md).
