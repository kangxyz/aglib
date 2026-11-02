# Finite normalization over a possibly nonaffine base

Source: [FiniteNormalization.lean](FiniteNormalization.lean).

Let `f : X ⟶ Y` be dominant and locally of finite type between integral
schemes, with invertible original `functionFieldMap f`.
Assume `topologicalKrullDim Y ≤ 2` and Nagata for every nonempty affine
chart of `Y`.
`genericNormalization_isFinite_of_birational` proves finiteness of the
original generic normalization arrow of `X`.

The proof chooses adapted affine charts over `Y`, applies `AdaptedCharts`,
and uses `genericNormalization_finite_app` for the original normalization
section map. No source regularity, normality, or resolution is needed.

When `f` is proper, `genericNormalization_comp_isProper` makes the
normalization followed by `f` proper. Later models can therefore retain
their accumulated map to the original Nagata surface.

Present consumers: [CommonModelOverBase](CommonModelOverBase.md), [PointStep](PointStep.md).
