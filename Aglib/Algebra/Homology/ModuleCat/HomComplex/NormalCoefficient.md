# Local concentration of the original coinduced coefficient

[NormalCoefficient.lean](NormalCoefficient.lean) starts with an actual finite
injective local map `sigma : R →+* A`, where R is a regular local ring of
dimension two and A is a normal Noetherian local domain of dimension two.
The supplied map is essential. The module does not construct it and does
not require completeness, a coefficient field, an assumed flatness condition
or a Cohen–Macaulay premise. The two ring carriers share the universe of the
existing finite-normal freeness theorem; the derived-category size remains
independent.

The coefficient `coinducedCoefficient sigma` is the native A-module
`Hom_R(A,R)`, using the original restricted R-module structure on A. Its
explicit linear equivalence to those functionals preserves the intrinsic
action `(a • phi)(b) = phi(b*a)`. For the actual coinduced complex J,
`regularSingleComplexIso J` identifies `Hom_A(A[0],J)` with J by evaluation
at `1_A`, including the native single-object comparison. This is an
isomorphism of A-module complexes. Its differential and naturality proofs
use the original single-cochain constructors and coefficient maps.

For an actual augmentation `u : R[0] → I` that is a quasi-isomorphism,
`coinducedCoefficientAugmentation` is the inverse native single comparison
followed by termwise coinduction of that same u. The existing
`IsRegularLocalRing.free_of_finite_normal_dimension_two` proves the needed
freeness; an explicit identity linear equivalence matches its original
algebra action to native scalar restriction. Exact projective coinduction
then proves that this original augmentation is a quasi-isomorphism.
There is no assumed coefficient-concentration statement.

`coinducedRegularHomAugmentation` expresses that map in the actual Hom
complex. Its evaluation equation recovers the original coinduced
augmentation. Its quasi-isomorphism proves that every homology group in
nonzero degree vanishes. `coinducedRegularHomologyZeroIso` identifies degree
zero with the same A-module of functionals, and its normalization equation
retains the original map on homology.

If I is also an actual complex of injectives supported in nonnegative
degrees, the existing right-adjoint theorem proves that J is K-injective.
`normalCoefficientDerivedIso` then identifies the genuine A-derived dual
of `A[0]` with `Hom_R(A,R)[0]`. Its factors are the original derived single
comparison, the published dual-localization comparison, and the inverse of
the localized Hom augmentation. No A-linearity is inferred from an
underlying R-linear arrow.

This supplies the coefficient term in the original nonsplit Postnikov
duality row. It is local coefficient concentration, not concentration of
the projective closed-embedding right-adjoint sheaf. Identifying that sheaf
with a canonical sheaf, matching geometric trace with the dual of the
original structural unit, and deriving GR or B7 boundedness remain
separate obligations. In particular, this calculation imposes no rationality
condition on A and does not split its surface cohomology complex.
