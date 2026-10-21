# Regularity of the actual regular-local point blowup

`AlgebraicGeometry.Scheme.Blowup.RegularPoint.regularStalks` proves that every
actual stalk of `(Scheme.Blowup.blowupDatum (affineCenter A (maximalIdeal A))).Y`
is regular local, for an arbitrary commutative ring `A` with native
`IsRegularLocalRing A` and `ringKrullDim A = 2`.

The theorem uses the same ordered parameters `firstParameter A hd` and
`secondParameter A hd` as the existing exceptional-projective-line comparison.
It imposes no excellence, Henselian, completeness, coefficient-field or
separately supplied regularity assumption.

For the first parameter chart, write `Q = A[T]/(a*T-b)`. The frozen comparison
identifies `Spec Q` by an open immersion with the original saturated chart of
the actual blowup. The original scalar `a` is a nonzerodivisor on `Q`.
Its principal ideal equals the extension of `(a,b)`, because `b=a*T` in `Q`.
The existing quotient comparison therefore identifies `Q/(a)` with
`(A/(a,b))[T]` through the original coefficient quotient and ratio coordinate.
For the maximal-ideal centre this is a polynomial ring over the original
residue field, hence regular.

`regularLocalRing_chartFibreToBlowup` localizes at the actual prime defined by
the original chart reduction map. The lower
`IsRegularLocalRing.atPrime_of_quotient_span_singleton` theorem lifts regularity
through `a`. The canonical spectrum-stalk comparison and the original open
chart's stalk isomorphism transport it to the actual blowup stalk.

`regularLocalRing_exceptionalι` uses the already proved covering by both
original fibre charts. The final theorem splits according to membership in
the range of the original quotient centre. The actual pullback range identity
handles that range, and `blowup_regular_away` handles its complement using the
regular stalks of the original spectrum.

This proves the regularity conclusion of [Stacks Lemma 54.3.2, tag
0AGR](https://stacks.math.columbia.edu/tag/0AGR), checked on 2026-10-22.
The native proof treats all fibre points directly. It uses the exceptional
chart slice corresponding to [Stacks Lemma 54.3.1, tag
0AGQ](https://stacks.math.columbia.edu/tag/0AGQ) and the regular-quotient lifting
argument of [Stacks Lemma 10.106.7, tag
00NU](https://stacks.math.columbia.edu/tag/00NU). These citations describe the
mathematical correspondence; no external theorem is assumed in the Lean proof.

Irreducibility, the normal bundle, contraction, factorization and minimal
models are separate conclusions, outside this leaf.
