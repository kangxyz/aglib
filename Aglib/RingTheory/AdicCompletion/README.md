# Adic completion

[FiniteModule](FiniteModule.lean), imported as `Aglib.RingTheory.AdicCompletion.FiniteModule`, proves completeness of finite modules over a Noetherian ideal-adically complete ring and of finite algebras for the extended ideal. Its base need not be local. [Formal-smooth lifting](../Smooth/AdicCompletion.lean) uses this completeness to lift actual quotient and tensor closed-fibre maps.

[DiscreteValuationRing](DiscreteValuationRing.lean), imported as `Aglib.RingTheory.AdicCompletion.DiscreteValuationRing`, equips `AdicCompletion (IsLocalRing.maximalIdeal R) R` with domain, DVR, and henselian local-ring structures for a domain DVR `R`. It uses the canonical completion algebra map and `FractionRing` carrier. The residue identification is the inverse of the induced residue-field map; selected residue markings and the fraction-field/constants triangles retain those actual maps.

The domain/DVR proof uses the [separated principal-maximal-ideal criterion](../LocalRing/SeparatedPrincipal.lean).

[TowerComparison](TowerComparison.lean), imported as `Aglib.RingTheory.AdicCompletion.TowerComparison`, constructs the canonical linear map from the native `AdicCompletion I M` to `ModuleCat.sectionsSubmodule Q` for an inverse tower indexed by all natural numbers, including zero. Its stage maps are the original quotient factors, and its composite with `AdicCompletion.of` is the original compatible family. A uniform shifted kernel bound and an eventual transition-range bound make this actual map a linear equivalence. The shifts can differ, and ring, source-module, and tower-module universes are independent. No Noetherianity, finite generation, or surjectivity of the tower transitions is assumed. These are explicitly conditional algebraic bounds, not a supplier of geometric formal functions or a topological comparison.

For a commutative ring `R`, ideal `I` and `R`-module `M`,
[CompatibleLifts](CompatibleLifts.md) takes maps `F n : M →ₗ[R] N n` with
transitions `ρ n : N (n + 1) →ₗ[R] N n`, assuming
`(ρ n).comp (F (n + 1)) = F n` and the explicit correction condition

```lean
(ρ n).ker ≤ (I ^ n • (⊤ : Submodule R M)).map (F (n + 1))
```

For a compatible family `x : ∀ n, N n`, if `N 0` is subsingleton,
`exists_compatible_cauchy_lift` constructs exact stage lifts forming a native
adic Cauchy sequence. If each `F n` also kills
`I ^ n • ⊤`, `exists_compatible_lift` returns an element of the native
completion whose evaluations, followed by the original quotient factors of
`F n`, are exactly the prescribed components. No Noetherianity, finite
generation or completeness hypothesis is imposed.

For `q : ℕ`, with the same compatibility, correction and annihilation conditions,
`exists_filtered_compatible_lift` replaces the zero-stage premise by `x q = 0`.
It lifts from the completion of the original submodule `I ^ q • ⊤`; the image
under completion of its actual inclusion has every prescribed original
component. The theorem asserts neither injectivity of this inclusion map on
completions nor equality of its image with a completed ideal power.

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

[FiniteLocalization](FiniteLocalization.md) treats a finite commutative
algebra `C` over a Noetherian local ring `B`, in the same universe, and an
original prime `p` of `C` contracting to the maximal ideal of `B`.
`FiniteLocalization.completionMap p hp` is the canonical same-precision
quotient-system extension of `B → C_p`. Its explicit `baseAlgebra p hp`
makes the actual completion of `C_p` finite over the maximal-adic
completion of `B`. The proof derives the finite residue-branch
decomposition from the Artinian residue quotient, radical powers and CRT.
It does not assume that the uncompleted localization `C_p` is finite
over `B`, and it needs no domain, flatness or coefficient-field premise.

## DVR coefficient conditions and finite-local transfer

[GeometricallyReducedFraction](GeometricallyReducedFraction.lean) defines
`AdicCompletion.HasGeometricallyReducedFractionCompletion R` for a domain
DVR: the fraction field of its actual maximal-adic completion is
geometrically reduced over `FractionRing R` under the canonical lifted
coefficient action. Characteristic zero supplies this condition through
perfectness of the original fraction field. [RegularGenericFormalFiber](RegularGenericFormalFiber.lean)
and [GenericFormalFiber](GenericFormalFiber.lean) derive it from the finite
generic formal-fibre tests; the [excellent-DVR interface](../Excellent/README.md)
supplies those tests from the G-ring component of standard excellence.
[SameUniformizer](SameUniformizer.lean) and
[ValuativeCompleteness](ValuativeCompleteness.lean) retain the actual DVR maps
and completed fraction-field valuation used in parameter extension.

[FiniteLocalApproximation](FiniteLocalApproximation.lean) transfers a supplied
maximal-adic approximation solver over a Noetherian local ring to every
proper-ideal completion of a finite local algebra in the same coefficient
universe. The finite equation and unknown types have independent universes.
It returns an exact solution, the literal original quotient projection and
membership of the error in the original extended ideal power. The
[DVR approximation results](../Henselian/DVRArtinApproximation.md) supply the
solver and construct the finite local model in their stated setting.

## Compatible systems and bounded reconstruction

[CompatibleSystemEffectivity](CompatibleSystemEffectivity.lean) makes the
native compatible-section module finite over `AdicCompletion I R` for an
`IsCompatibleSystem I F`. For `I.FG`, its canonical reductions recover the
original stages and their transition maps. For the same `I.FG` hypothesis,
[CompatibleSystemComplete](CompatibleSystemComplete.lean) proves completeness
for the original ideal, and
[CompatibleSystemHom](CompatibleSystemHom.lean) gives the completed-linear
map of compatible families across independent carrier universes.
[CompatibleSystemBounds](CompatibleSystemBounds.lean) transports uniform
stage bounds to the limit; its cokernel bound retains separation of the
actual cokernel and finite generation of `I`.

[BoundedReconstruction](BoundedReconstruction.lean) treats a Noetherian
commutative ring `R`, a finite `AdicCompletion I R`-module `M`, a finite
`R`-module `N` and a
completed-linear map `f : M →ₗ[AdicCompletion I R] AdicCompletion I N`, all in
the ring universe. If a single power of `I` kills both defects of the
restricted map, the native pullback along `AdicCompletion.of I N` is finite
over `R`, and its completed first projection is the canonical equivalence
with `M`. [BoundedReconstructionUnique](BoundedReconstructionUnique.lean)
retains the finite candidate's original bounded map to `N`, its specified
completion equivalence and their commuting equation. The affine Grothendieck-existence
construction uses these comparisons; finiteness of an arbitrary completed
module over the uncompleted ring is not a conclusion.

## Local regularity and actual finite-algebra descent

[RegularLocalRing](RegularLocalRing.md) identifies regularity and dimension of
a Noetherian local ring with those of its original maximal-adic completion.
[The completed-stalk comparison](../../AlgebraicGeometry/Spec/CompletionLocalRing.md)
retains the actual scheme point, scalar map and proper global regularity
comparison. [PrincipalDiscreteValuationRing](PrincipalDiscreteValuationRing.md)
constructs the literal principal completion and its original residue comparison.

[CompleteParameterMap](CompleteParameterMap.md) completes an original local
parameter map into a complete Noetherian local ring. Maximal-radical image and
original residue surjectivity derive module finiteness; a regular source and
matching finite dimensions derive injectivity.

[FiniteReducedDescent](FiniteReducedDescent.md) descends reducedness of the
actual base completion along an original finite injective algebra map when
the actual completed maximal localizations are reduced. Its branch comparison
uses the public all-level evaluation interface of
[FiniteLocalization](FiniteLocalization.md).
[AssociatedPrimeCriterion](AssociatedPrimeCriterion.md) gives analytic
reducedness criteria with their actual associated-prime DVR and
reduced-prime-completion inputs explicit.

## Actual finite-algebra branches and degree

[FiniteSemilocal](FiniteSemilocal.md) identifies the completed-base tensor
of a finite algebra over a Noetherian local ring with the finite product of
its actual completed local branches. The original scalar and quotient maps
are retained; the uncompleted localization need not be finite.
[FiniteSemilocalDegree](FiniteSemilocalDegree.md) embeds each branch in a
free module of the original generic degree by first embedding the whole
finite domain algebra and then completing that injection. Domain hypotheses
on the relevant completions are retained for fraction-field degree bounds;
regularity supplies the base completion's domain property where stated.
These are inputs to complete-local degree induction, not that induction
or a resolution theorem.
