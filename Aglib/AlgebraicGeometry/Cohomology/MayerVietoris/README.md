# Two-open and two-affine cohomology

[InjectiveComplex](InjectiveComplex.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.InjectiveComplex`, constructs the genuine two-open section sequence on actual injective module-sheaf complexes. Its maps are the original restrictions and their difference, with the specified binary cover.

[AffineComparison](AffineComparison.lean) gives `Scheme.Modules.twoAffine_isZero_rightDerived_add_two`: two supplied affine open immersions covering the scheme and a supplied affine intersection give vanishing in degrees at least two for the stated quasicoherent coefficients. The cover and intersection hypotheses are retained.

[FirstCohomology](FirstCohomology.lean) identifies first derived global sections with the actual restriction-difference cokernel through `twoAffineRightDerivedOneIsoCokernel`. `twoAffine_isZero_rightDerived_one_of_difference_surjective` additionally requires surjectivity of the actual difference map. Higher two-affine vanishing alone does not supply that H1 premise.

Lower [topological Mayer–Vietoris](../../../Topology/Sheaves/README.md), affine derived-section acyclicity and resolution H0 comparisons feed these maps. The first-cohomology comparison and external two-open consumers use the result, without a curve or projective-line hypothesis.
