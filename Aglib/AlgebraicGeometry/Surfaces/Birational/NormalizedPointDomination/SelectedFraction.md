# A local fraction for the selected curve

Source: [SelectedFraction.lean](SelectedFraction.lean).

For a dominant map `p : X ⟶ Y` of integral schemes with invertible original
function-field map, `exists_local_fraction_of_transcendental_residue`
takes a source-stalk element whose residue is transcendental under
`p.residueFieldMap`. It proves that element a unit and constructs nonzero
`a,b` in the actual target maximal ideal with
`u * p.stalkMap z b = p.stalkMap z a`.

Surjectivity of the original field map and the target stalk's fraction-field
structure supply the fraction; `functionFieldMap_stalk` gives its equation.
A unit denominator contradicts residue transcendence, and locality then
excludes a unit numerator.

`SelectedElimination` retains this pair through its finite DVR-order
induction. `RetainedFraction` proves maximal-ideal membership for arbitrary
retained pairs, and `SelectedStep` supplies exceptional division and strict
order decrease. The outer curve-count induction is in `CardinalityInduction`.

Present consumers: [RetainedFraction](RetainedFraction.md), [SelectedElimination](SelectedElimination.md).
