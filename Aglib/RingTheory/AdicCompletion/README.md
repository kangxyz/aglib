# Adic completion

[FiniteModule](FiniteModule.lean), imported as `Aglib.RingTheory.AdicCompletion.FiniteModule`, proves completeness of finite modules over a Noetherian ideal-adically complete ring and of finite algebras for the extended ideal. Its base need not be local. [Formal-smooth lifting](../Smooth/AdicCompletion.lean) uses this completeness to lift actual quotient and tensor closed-fibre maps.

[DiscreteValuationRing](DiscreteValuationRing.lean), imported as `Aglib.RingTheory.AdicCompletion.DiscreteValuationRing`, equips `AdicCompletion (IsLocalRing.maximalIdeal R) R` with domain, DVR, and henselian local-ring structures for a domain DVR `R`. It uses the canonical completion algebra map and `FractionRing` carrier. The residue identification is the inverse of the induced residue-field map; selected residue markings and the fraction-field/constants triangles retain those actual maps.

The domain/DVR proof uses the [separated principal-maximal-ideal criterion](../LocalRing/SeparatedPrincipal.lean).

[TowerComparison](TowerComparison.lean), imported as `Aglib.RingTheory.AdicCompletion.TowerComparison`, constructs the canonical linear map from the native `AdicCompletion I M` to `ModuleCat.sectionsSubmodule Q` for an inverse tower indexed by all natural numbers, including zero. Its stage maps are the original quotient factors, and its composite with `AdicCompletion.of` is the original compatible family. A uniform shifted kernel bound and an eventual transition-range bound make this actual map a linear equivalence. The shifts can differ, and ring, source-module, and tower-module universes are independent. No Noetherianity, finite generation, or surjectivity of the tower transitions is assumed. These are explicitly conditional algebraic bounds, not a supplier of geometric formal functions or a topological comparison.

[EquivTransport](EquivTransport.lean) composes native completion congruence with
a given linear comparison over a fixed base ring, preserving the original
base-ring scalars and class map across independent module universes.

[RingEquiv](RingEquiv.lean) defines `AdicCompletion.congrRingEquiv` for a ring
equivalence `e : R ≃+* S` between commutative rings and an ideal `I` of `R`. It identifies
`AdicCompletion I R` with `AdicCompletion (I.map e.toRingHom) S` across independent
ring universes, using the actual finite quotient equivalences `quotientPowEquiv`.
The maps preserve original elements, every quotient projection and transition,
and the extended ideal powers (`congrRingEquiv_map_power`). No finite-generation,
Noetherianity or completeness premise is required.
[RingEquivApproximation](RingEquivApproximation.lean) gives
`AdicCompletion.exists_solution_of_ringEquiv_solver`: a solver in the mapped-ideal
completion yields an exact solution in the original ring, retaining both its
literal quotient-projection equality and its extended-ideal error. The solver
remains a premise of this transport helper; the
[geometric-local Henselization endpoint](../Henselian/GeometricLocalArtinApproximation.md)
constructs the model and supplies that solver.

[HomComparison](HomComparison.lean) defines `AdicCompletion.quotientHomEquiv`:
maps into an adically complete module are exactly compatible maps on the
original ideal-power quotients, with native `LinearMap.reduceModIdeal` as the
forward map. The source need not be finite or complete.

[CompletedHom](CompletedHom.lean) identifies completion of Hom between finite
modules over a Noetherian ring with Hom between their completions. The modules
lie in the ring universe, as required by the native finite-module completion
comparison. The forward map extends `AdicCompletion.map`.
[QuotientComparison](QuotientComparison.lean) identifies reductions of a
completion with original reductions for a finitely generated ideal, retaining
evaluation and transition maps. [FormalHom](FormalHom.lean) consequently
identifies compatible quotient maps with completed-linear maps for arbitrary
modules and a finitely generated ideal; its finite Noetherian specialization
identifies this compatible Hom system with completion of Hom. No nonflat
finite-stage Hom base-change assertion is used.

[NoetherianRing](NoetherianRing.lean) gives the Noetherian ring instance for
completion of a Noetherian commutative ring along any ideal. Its construction
uses a finite polynomial presentation of the ideal and the native finite-variable
power-series comparison; no locality, completeness or chosen generators remain
as premises.

[CompatibleSystem](CompatibleSystem.lean) defines `AdicCompletion.IsCompatibleSystem`
on a native module-valued inverse tower: finite stages, ideal-power annihilation,
surjective successor maps and their exact ideal-multiple kernels. It retains
the quotient/transition equation, includes the zero stage and allows independent
ring and stage universes. [CompatibleSystemGenerators](CompatibleSystemGenerators.lean)
lifts one finite free family whose projection generates every stage. These
statements do not assert finite generation of the inverse limit over the
possibly incomplete original ring.

[Ext](Ext.lean) gives uniqueness for base-ring-linear maps from completions
into separated targets and the corresponding bilinear uniqueness result,
without module finiteness. [ExtendedHom](ExtendedHom.lean) extends Hom evaluation
for an ideal of a smaller structural ring, requiring finiteness only over the
larger Noetherian coordinate ring and retaining the original class evaluations.

[FilteredKernelGeneration](FilteredKernelGeneration.lean) gives finite
filtration descent for relation modules, a quotient span-generator lifting
criterion and its nilpotent Nakayama consequence. The filtration need not be
adic. The successive-generation premises remain explicit in these algebraic
helpers; the final projective geometric consumer supplies them.

[Congruence](Congruence.lean) identifies the kernel of `AdicCompletion.evalₐ I n`
with the extension of `I ^ n` for a finitely generated ideal. Equality of
projections is equivalent to membership of the difference in that ideal,
including `n = 0`. `mkₐ_comp_eq_evalₐ_comp_iff` expresses the same precision
condition for literal compositions of algebra maps.

[CofinalIdeals](CofinalIdeals.lean) compares the native completions of ideals
with specified cofinal power bounds. [FiniteLocalCofinality](FiniteLocalCofinality.lean)
supplies the power bound for the extended maximal ideal of a finite algebra
between local rings, using its Artinian closed fiber. For a local structural
map, `finiteLocalAlgEquiv` compares the extended-maximal-ideal and maximal-ideal
completions, with their original quotient projections. No Noetherian premise
is needed for this cofinality comparison.

[ApproximationTransfer](ApproximationTransfer.lean) transfers exact solvability
over a larger-ideal completion to approximation for a smaller finitely generated
ideal by affine substitution. [FiniteAlgebraApproximation](FiniteAlgebraApproximation.lean)
transfers approximation over a Noetherian ring to a finite algebra in the same
universe, without requiring a free algebra module. Both helpers retain their
solver premise; the [polynomial-origin Henselization results](../Henselian/README.md)
supply it in their stated setting.
