# A transcendental element in the curve-generic residue field

Source: [GenericResidueSection.lean](GenericResidueSection.lean).

For an irreducible closed curve contracted by a proper `p : X ⟶ Y`,
`exists_transcendental_curve_residue` constructs an element of the original
ambient stalk at its generic point whose residue is transcendental for
`p.residueFieldMap`.

It uses the integral curve and structural map of `CurveResidue`. Pullback
from its nonempty affine chart through the original dominant generic
field point is injective. The section-map triangle preserves the original
image-point scalar action. The transcendental section then lifts through
the original ambient residue quotient.

Together with `SelectedFraction`, this supplies the initial retained
fraction in selected-curve elimination.

Present consumers: [SelectedElimination](SelectedElimination.md).
