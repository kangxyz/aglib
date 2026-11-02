# Full exceptional Hilbert numerics over the original residue field

Source: [Projective.lean](Projective.lean).

`exceptional_hilbert_of_inverseLine_cohomology` uses the actual padded
exceptional tautological embedding and the already proved closed-point CM
parameters of the full exceptional scheme. Ordinary field-extension
cohomology removes any need for a finite Cartier representative or rational
point over the original residue field. The only additional numerical inputs
are actual H0 vanishing and H1 dimension one of the inverse exceptional line.

The original exceptional power/H0 and Rees-component comparisons then give
`dim gr_m(A)_r = 2r+1` in every degree over the original residue field. The
native first-power cotangent comparison derives cotangent dimension three;
Noetherian minimal generator cardinality then constructs three original
maximal-ideal generators. No embedding-dimension or Hilbert-function formula
is assumed in these statements.

For any original ordered generating triple, the existing unique
`CaseOne.exists_presentation_of_hilbert` produces the nonzero homogeneous
quadratic, the entire original canonical cone kernel, and the actual
saturated chart exceptional quotient with its original coefficient and
fraction laws. No presentation is guessed or supplied as a geometric result.

The inverse-line cohomology must still be supplied from the honest original
canonical identification and coefficient Serre duality. Rationality alone
is not claimed to imply it: a regular local surface has a different
exceptional degree. This leaf does not prove the missing canonical
identification, Gorenstein preservation, Case-II marker, or finite tree
termination. It never assumes child completeness, perfection, equality of
residue fields, or finiteness of child local rings over the original base.

Present consumers: [QuadraticClassification](../QuadraticClassification.md).
