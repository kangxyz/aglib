# Two-open and two-affine cohomology

[InjectiveComplex](InjectiveComplex.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.InjectiveComplex`, constructs the genuine two-open section sequence on actual injective module-sheaf complexes. Its maps are the original restrictions and their difference, with the specified binary cover.

[AffineComparison](AffineComparison.lean) gives `Scheme.Modules.twoAffine_isZero_rightDerived_add_two`: two supplied affine open immersions covering the scheme and a supplied affine intersection give vanishing in degrees at least two for the stated quasicoherent coefficients. The cover and intersection hypotheses are retained.

[FirstCohomology](FirstCohomology.lean) identifies first derived global sections with the actual restriction-difference cokernel through `twoAffineRightDerivedOneIsoCokernel`. `twoAffine_isZero_rightDerived_one_of_difference_surjective` additionally requires surjectivity of the actual difference map. Higher two-affine vanishing alone does not supply that H1 premise.

Lower [topological Mayer–Vietoris](../../../Topology/Sheaves/README.md), affine derived-section acyclicity and resolution H0 comparisons feed these maps. The first-cohomology comparison and external two-open consumers use the result, without a curve or projective-line hypothesis.

[Geometric](Geometric.lean) identifies actual inverse image of the native
open-free Mayer–Vietoris short complex with the native short complex on the
inverse-image opens. `zariskiCohomologyOpenMap` is the original exact-inverse-image
Ext map, using the normalized open-free comparison and the supplied actual
coefficient arrow. `mayerVietoris_delta_geometric` proves that these forward
maps commute with the native connecting homomorphism, through the actual
extension class; `mayerVietoris_delta_coefficient` gives coefficient
naturality. All additive coefficient sheaves and scheme morphisms are
arbitrary. These compatibility lemmas impose no quasicoherence, flatness or
separation hypothesis and do not assert a base-change endpoint by themselves.

[Geometric/Coefficients](Geometric/Coefficients.lean) proves the exact
coefficient square for `zariskiCohomologyOpenMap`, using a supplied commuting
square of actual pullback coefficient arrows. This comparison gives structural
semilinearity of the original open-cohomology map without changing its Ext
objects or forward maps.

[Geometric/Composition](Geometric/Composition.lean) proves
`zariskiCohomologyOpenMap_comp_app` and the corresponding natural-transformation
equation. Successive original geometric maps equal the original map for the
composite morphism, with the actual composite coefficient arrow transported
through the native adjunction comparison. The actual inverse-image opens
agree definitionally; no base-change, quasicoherence or separation premise
is used.

[GeometricTop](GeometricTop.lean) proves
`sheafHPrimeTopAddEquiv_geometric`: the geometric native open-cohomology map
at the whole space is exactly the original `zariskiCohomologyMap` on
`Sheaf.H`. Its generator comparisons identify the original open-free and
constant-sheaf pullback isomorphisms through their actual represented-section
and adjunction-unit formulas, for arbitrary scheme morphisms and additive
coefficients.

[Scalars](Scalars.lean) puts the same native Mayer–Vietoris sequence in
modules over a specified structural ring. `moduleMayerVietorisDelta` is the
original connecting map, proved linear through coefficient naturality.
`moduleMayerVietorisSequenceForgetIso` uses the native binary-biproduct
comparison to recover every original additive arrow, and
`moduleMayerVietorisSequence_exact` reflects the native exactness through
faithful exact scalar forgetting. `moduleHPrimeTopLinearEquivOfHom` retains
the original whole-space cohomology comparison and structural action.
Coefficients remain arbitrary; neither quasicoherence nor flatness is used
to construct this exact module sequence.

[Scalars/Zero](Scalars/Zero.lean) proves that the original degree-zero sum
of restriction maps is monomorphic with its actual structural scalars.
It uses the epimorphism in the native free-open Mayer–Vietoris sequence and
the native degree-zero Ext precomposition lemma, then faithful scalar
forgetting. No acyclicity, affine-open or quasicoherence premise is used.
