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

The comparison with base-ideal formal-functions quotients and the projective
completion equivalence are developed in
[GrothendieckExistence](../../../Cohomology/GrothendieckExistence/README.md).
That comparison preserves the original quotient maps and transitions.
