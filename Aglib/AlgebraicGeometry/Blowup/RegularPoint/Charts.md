# Polynomial charts in the actual exceptional fibre

This consumer uses exactly
`Scheme.Blowup.blowupDatum (affineCenter A I)` and its proved saturated affine
atlas. It defines the exceptional fibre as the literal pullback of its
blowdown along the original quotient immersion `Spec(A/I) → Spec(A)`.

For `I = (a,b)` with `a` regular on `A` and `b` regular on `A/(a)`, the proved
ring comparison from `RingTheory/Blowup/RegularPair` produces an actual
polynomial chart on this fibre. `chartFibreSquare` is the native quotient
pullback square after the original ring isomorphism. The two equations
`fibreChart_fst` and `fibreChart_snd` retain the original atlas inclusion and
polynomial projection. `fibreChart_isPullback` identifies this map as the
pullback of the original saturated chart, proving its openness and image.

When the opposite orientation is regular as well, `fibreCharts_cover` proves
coverage by these same two maps. The generating-pair equation supplies
coverage through the existing `AffineAtlas.generator_covers`; no atlas,
covering family, or exceptional-fibre equivalence is assumed.

The original polynomial quotient also gives `rawChart` in the same blowup.
Its reduction is precisely the earlier fibre chart, and
`rawChart_reciprocal` compares the two original quotient-chart maps after
inverting the first coordinate. This equality uses universal uniqueness on
the actual open Cartier overlap before reduction. It does not apply that
uniqueness principle to maps supported on the exceptional fibre.

The actual reciprocal map is reduced to the original Laurent algebra.
`fibreCharts_laurent_compatibility` retains the positive and inverse Laurent
maps. The atlas overlap range, together with the forward ratio equation,
proves the exact Laurent intersection. `twoChartExceptionalOverIso` then
identifies the original two-chart pushout with the literal exceptional fibre
over the original quotient ring. The regular-local consumer uses this same
comparison to reach native projective P1.

The comparison of actual kernel-ideal frames with projective twists remains
a separate normal-line obligation. The intended source calculation is
[Stacks, Lemma 54.3.1, tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ).
Compilation status is recorded separately against the exact source bytes.
