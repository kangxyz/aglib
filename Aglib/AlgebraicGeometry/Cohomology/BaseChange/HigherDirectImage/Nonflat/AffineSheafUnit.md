# Unit evaluation for arbitrary original affine presentations

Source: [AffineSheafUnit.lean](AffineSheafUnit.lean).

`affineMapOfTilde_unit_apply` retains the original native `affineMapOfTilde`,
source presentation e, target presentation arrow c, and scalar-extension map t.
It sends the geometric pullback unit of the original section supplied by e at x
to the original section supplied by c at t(1 tensor x). The target arrow c need
not be invertible, and the target sheaf has no quasicoherence hypothesis.

The proof uses the existing single-map `tildePullbackIso_globalSections_unit`,
unit naturality, and cancellation of the given e with its actual inverse.
It does not assume a two-map unit square or invoke the desired composition law.
The existing AffineSheaf and TildePullbackRaw source files remain unchanged.

AffineSheafComposition derives its two-step unit identity from native
`pullbackCongr_unit_top` and `pullbackComp_inv_unit_top`, then uses this formula
twice and the actual scalar-extension composition/unit formulas. The independent
lower PresentationUnits leaf supplies equality detection using existing
adjunction Hom equivalences. This is a different native proof route, not a new
general mate-composition implementation.
