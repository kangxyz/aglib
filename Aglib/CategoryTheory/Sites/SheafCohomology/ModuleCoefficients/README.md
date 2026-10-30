# Module and underlying abelian cohomology

| Source | Interface |
| --- | --- |
| [Acyclic](Acyclic.lean), [InjectiveAcyclic](InjectiveAcyclic.lean) and [InjectiveAcyclicSlice](InjectiveAcyclicSlice.lean) | Actual injective module sheaves are acyclic for original abelian sheaf cohomology, on the site and its actual slices. The proof does not assume scalar forgetting preserves injectives. |
| [Comparison](Comparison.lean), [DerivedExt](DerivedExt.lean) and [DerivedGamma](DerivedGamma.lean) | Original module-Ext/abelian-`Sheaf.H` comparisons in every degree and actual module evaluation `rightDerived` comparison. |
| [DerivedScalarSections](DerivedScalarSections.lean), [DerivedSlice](DerivedSlice.lean), [Restriction](Restriction.lean) | Original scalar restriction and slice maps, including the actual `restrictScalars` on coefficient-valued sections. |
| [DerivedBoundary](DerivedBoundary.lean), [ExtBoundary](ExtBoundary.lean) | Additive Gamma long exact sequence with boundary normalized through the original short-exact-sequence Ext class. |
| [UniqueFamily](UniqueFamily.lean) | The original sheafified free Cech tuple term of a unique-indexed family, compared with the free abelian sheaf on its actual iterated product. |
| [Etale cohomology](../../../../AlgebraicGeometry/EtaleCohomology/Coefficients/Cohomology.lean), [derived cohomology](../../../../AlgebraicGeometry/EtaleCohomology/Coefficients/DerivedCohomology.lean) and [derived slice cohomology](../../../../AlgebraicGeometry/EtaleCohomology/Coefficients/DerivedSliceCohomology.lean) | Concrete small-etale entries with the required existence and universe hypotheses discharged, owned by the geometric family. |

The constant-ring action comes from the constant-sheaf adjunction unit; it does
not identify a constant ring with all global ring sections. The boundary is
additive: this interface does not assert a separately chosen native
right-derived long-exact-sequence boundary or module-linearity of the long exact
sequence. Concrete consumers are in
[EtaleCohomology](../../../../AlgebraicGeometry/EtaleCohomology/README.md).

[DerivedExt](DerivedExt.lean) and [RepresentedSections](RepresentedSections.lean)
specialize the [represented Ext/right-derived comparison](../../../../Algebra/Homology/RightDerived/Represented.lean).
[DerivedGamma](DerivedGamma.lean) retains the public module names for the
[additive postcomposition constructors](../../../../Algebra/Homology/RightDerived/Postcomp.lean).
The [intrinsic Global interface](../Global/Comparison.lean) represents additive
module sections by the actual lifted rank-one module. Its comparison with
evaluation uses [Terminal/Comparison](../Terminal/Comparison.lean) and an
explicit terminal object.

[RingAction](RingAction.lean) constructs scalar endomorphisms from the original
natural ring-section cone and one lifted additive coefficient. Its cohomology
action uses the actual `H.map`, with the original multiplication order and
Frobenius square. Scheme-specific section and characteristic facts remain in
the native consumer.
