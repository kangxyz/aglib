# Coherent adic systems

[Basic](Basic.lean) defines
`AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem X K` for an arbitrary
ideal-sheaf datum `K` on a locally Noetherian scheme. The underlying objects
are functors `ℕᵒᵖ ⥤ X.Modules`, and morphisms are their actual natural
transformations. The term at index `n` is coherent and killed by `K ^ n`.
Its original successor transition factors through an isomorphism from the
actual closed-thickening quotient, with the original pullback/pushforward
adjunction unit. Index zero is zero; index one is the special fibre.

[Quotient](Quotient.lean) constructs canonical reduction maps and nested
reduction comparisons, retaining their original-unit equations.
[Completion](Completion.lean) constructs
`completionFunctor : X.CoherentSheaf ⥤ AdicSystem X K` from the actual
closed-thickening quotients. This construction needs neither completeness
nor an effectivity hypothesis.

[Transitions](Transitions.lean) extends adjacent compatibility to the
canonical reductions between all levels. [Naturality](Naturality.lean)
proves that actual natural transformations intertwine these reductions.
[AssociatedGraded](AssociatedGraded.lean) constructs the coherent transition
kernels and their native coproduct, with split component maps.

[AmbientExact](AmbientExact.lean) proves that completion followed by
`adicSystemToDiagram` preserves finite colimits and zero morphisms.
These results concern the ambient diagram category. No levelwise abelian
structure or categorical kernel construction is installed on `AdicSystem`.

The comparison with base-ideal formal-functions quotients and the proper and projective
completion equivalences are developed in
[GrothendieckExistence](../../../Cohomology/GrothendieckExistence/README.md).
That comparison preserves the original quotient maps and transitions.

[QuotientSystem](QuotientSystem.lean) takes the termwise quotient of an
`I`-adic system by an independent ideal sheaf `K`, retaining `I`-adicity and
the original quotient units and transitions. [QuotientReductionSystem](QuotientReductionSystem.lean)
constructs nested reduction comparisons and the entire `K`-power quotient
tower. [QuotientInterchange](QuotientInterchange.lean) and its
[naturality](QuotientInterchangeNaturality.lean) interchange the two actual
closed-thickening quotients, preserving their original unit composites.
These constructions do not declare an arbitrary kernel diagram adic.

[QuotientCompletion](QuotientCompletion.lean) compares the independent
quotient of a coherent completion with completion of the coherent quotient.
[QuotientCompletionUnit](QuotientCompletionUnit.lean),
[QuotientCompletionCoefficient](QuotientCompletionCoefficient.lean), and
[QuotientCompletionNaturality](QuotientCompletionNaturality.lean) retain the
original coherent quotient unit, coefficient maps, ideal reductions, and
whole-tower naturality. The hypotheses are local Noetherianity and the
specified ideal sheaves; no base completeness or effectivity is used.

[PullbackQuotient](PullbackQuotient.lean) transports the original quotient
and its unit under arbitrary pullback for quasicoherent coefficients.
[OpenIdealPowers](OpenIdealPowers.lean) preserves powers of any ideal sheaf
under open restriction, including an independent exceptional ideal.
[QuotientFactorization](QuotientFactorization.lean) obtains natural diagram
factorizations from pointwise factorizations through the original epimorphic
quotient units. [UnitComparisons](UnitComparisons.lean),
[QuotientComparisonTransport](QuotientComparisonTransport.lean), and
[QuotientCongr](QuotientCongr.lean) retain the entire unit-compatible diagram
when components or ideal indices are transported. The
[two-ideal reconstruction](../../../Cohomology/GrothendieckExistence/Proper.md#same-ideal-reconstruction-and-two-ideal-effectivity)
uses these comparisons while keeping the defining and exceptional ideals
distinct.
