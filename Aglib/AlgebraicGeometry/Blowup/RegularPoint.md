# The actual exceptional projective line

The public construction `exceptionalOverIsoProjectiveP1` concerns exactly the
literal residue-field pullback of
`Scheme.Blowup.blowupDatum (affineCenter A (maximalIdeal A))`. Its hypotheses
are a commutative regular local ring and `ringKrullDim A = 2`.
No completeness, Henselianity, excellence, residue-field perfectness, or
characteristic assumption is added.

`IsRegularLocalRing.exists_regularPair` supplies the actual parameters.
The chosen pair defines the actual saturated blowup charts. Their polynomial
fibre identifications retain the original base maps and ratio coordinates;
the proved reciprocal map gives the original Laurent transition. The native
open-pushout criterion and native two-chart/projective-Proj comparison then
give the isomorphism over the original residue field.

`exceptionalOverIsoProjectiveP1_hom_over` retains the literal fibre projection.
`firstFibreChart_projectiveP1` and `secondFibreChart_projectiveP1` retain the
original parameter charts and identify them with the native standard charts.
The parameter choice is made once and used by all these maps and equations.

`quotientCentreIso` and `centreFibreIso` compare the actual ideal-sheaf centre
and its inverse-image subscheme with the original quotient fibre.
`centreFibreIso_hom_ι` retains the actual inclusion into the blowup, and
`centreStructureMap_immersion` retains the original structural triangle.
`centreOverIsoProjectiveP1` gives the corresponding isomorphism for that same
inverse-image-centre subscheme.

The normal-line identification remains further work; no normal-degree,
contraction, factorization, or minimal model theorem is supplied here.
The geometric source locator is
[Stacks, Lemma 54.3.1, tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ).
The adjacent regularity result is [Lemma 54.3.2, tag 0AGR](https://stacks.math.columbia.edu/tag/0AGR).
Native compilation status is kept separately against exact source hashes.
