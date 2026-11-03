# Original projective coordinates on a prescribed principal open

[UnitCoordinates](UnitCoordinates.lean) retains affine multiplication under
the native pullback-unit comparison.
[PrincipalOpen](PrincipalOpen.lean) constructs the canonical lift of a
prescribed principal open to the original coordinate-ideal blowup, with
its structural triangle and localized coordinates.

[AffineAgreement](AffineAgreement.lean) proves that the actual blowup map
to projective space agrees there with the original scalar-coordinate map.
[PrincipalAffineChart](PrincipalAffineChart.lean) gives a proper extension
of a finite tuple on `Spec A[1/f]` when `A` is Noetherian.
The base ring may be reducible or nonreduced. These principal-open
comparisons supply the original maps used by projective-extension and
regular-source domination; they do not replace the separate arbitrary-open
gluing argument.

Present consumers include [Agreement on the entire inverse image of a principal open](PrincipalRestriction.lean), [Actual agreement on the unit locus of affine coordinate ideals](AffineAgreement.lean).
