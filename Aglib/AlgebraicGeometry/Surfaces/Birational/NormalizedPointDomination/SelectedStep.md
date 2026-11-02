# Decrease at a normalized point step

Source: [SelectedStep.lean](SelectedStep.lean).

`exists_decreasing_fraction_at_normalizedPoint` uses integral `Z,Y,S`,
locally Noetherian `Z,Y` with integrally closed stalks, a closed nongeneric
`x : S`, and a locally finite-type literal normalized point blowdown `r`.
Its square is `f ≫ q = p ≫ r`, with `p : Z ⟶ normalizedPointBlowup S x`.
A codimension-one point `c : Z` has `q(f c) = x`, closed `p c`,
dimension-one image stalk on `Y`, and invertible original `f.stalkMap c`.

Given the retained fraction `u * q.stalkMap b = q.stalkMap a`, both
images nonzero, and transcendence of the residue of `u`, it constructs
the exceptional generator and transformed numerator and denominator.
Their images are nonzero, retain the pulled-back fraction equation,
lie in the new target maximal ideal, and have strictly smaller finite
DVR orders.

`ExceptionalGenerator`, the original stalk-map square, finite
image-point residue extension, `FractionTransform` and `RetainedFraction`
give these conclusions. `SelectedElimination` supplies the surviving-curve
geometry when using this local theorem in its finite recursion.

Present consumers: [SelectedElimination](SelectedElimination.md).
