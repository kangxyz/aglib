# Maximal-ideal membership of a retained fraction

Source: [RetainedFraction.lean](RetainedFraction.lean).

For any scheme map `p`, `fraction_mem_maximalIdeal_of_transcendental_residue`
takes a source-stalk element `u` whose original residue is transcendental
under `p.residueFieldMap`, and the equation
`u * p.stalkMap z b = p.stalkMap z a`.
It proves that these same target-stalk elements `a,b` lie in its maximal
ideal.

A unit denominator would make the residue of `u` a target scalar.
A unit numerator would force the denominator to be a unit by locality.
This local statement needs no domain, birationality or nonvanishing premise.
It applies to the same transformed fraction after exceptional division;
the fraction and its induction order are not reselected.

Present consumers: [SelectedStep](SelectedStep.md).
