# Finite presentation of an ideal quotient

`ModuleCat.IdealPresentation` retains finite free generators and relations
of the original ideal. `ofNoetherian` uses Mathlib's existing finite-module
presentation theorem. The cochain has the original ring in degree zero,
finite free terms in degrees minus one and minus two, and zero elsewhere.
Its augmentation in degree zero is the original quotient projection.

The augmentation cone is cohomologically at most minus three. Its canonical
precomposition map is therefore an additive Hom equivalence into an object
bounded below by minus one. The image of the augmentation under an additive
functor preserving finite colimits still identifies H0 with the image of the
original quotient.

`exists_annihilating_homotopy` constructs both maps and proves the literal
two-stage identities for each element of the ideal. These identities control
degree-minus-one homology after additive base change. They make no claim
about the bottom homology or about a full projective resolution.
`mappedHomology_neg_one_scalar_eq_zero` proves the resulting annihilation
for every additive linear functor; exactness is unnecessary.

The consumer is the original residue-Hom calculation in
`AlgebraicGeometry/Cohomology/Proper/ResidueVanishing`.
