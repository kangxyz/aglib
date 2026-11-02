# Native functors and their comparisons

[IsoLifting](IsoLifting.lean) transports a prescribed isomorphism lift
through a given natural functor-square comparison, using a fully faithful
source comparison and a faithful target comparison. It preserves equality
with the original forward map. Actual affine line-bundle lifting uses it
to pass through the canonical affine-spectrum isomorphisms.

[KanExtension](KanExtension/README.md) gives the native opposite Kan-extension
monomorphism criterion used by exact open extension by zero.
[Sections](Sections/README.md) identifies the original compatible sections
with evaluation at an initial object. Both families keep the native
functors and their original maps.

[Derived](Derived/README.md) retains native right-derived descents and proves
shift compatibility from their original unit squares.

[Flat](Flat.lean) gives pointwise left Kan-extension comparisons and finite-limit
preservation for large set-valued and abelian presheaves, retaining the separate
object and morphism universes and representable-flatness hypothesis.
[DiagramLift](DiagramLift.lean), [ModelAutomorphisms](ModelAutomorphisms.lean),
and [NaturalityTransport](NaturalityTransport.lean) transport actual diagrams,
natural automorphisms and their comparison maps through the displayed model
functors. Their finite-etale consumers supply the required model data.

[AutomorphismTransport](AutomorphismTransport.lean) gives `Functor.mapIso_conjugate` and
`NatIso.mapAut_conjugate`, using the original functor maps, natural-isomorphism
components and `Aut.autMulEquivOfIso`.

[MapComparisonSquare](MapComparisonSquare.lean) transports original map squares through natural functor
comparisons and objectwise coordinate isomorphisms. Its shared compatibility
predicate preserves the displayed composites and separate category universes.

[CoefficientSquare](CoefficientSquare.lean) assembles an ordinary coefficient
square on the values of one functor into abelian groups and one indexed
object/value family. Equality transport is derived from that same family;
the original elementary composition and coefficient-naturality equations
then give the complete value square. The native small-etale H1 coefficient
comparison supplies its original values to this construction.

[ComparisonPasting](ComparisonPasting.lean) constructs one comparison from a
section transformation and a coefficient transformation. Its whole composition
and transport laws give a `CommSq` from the original whole unit and relative
coefficient equations, with explicit functor associators. The section target
is arbitrary, object and hom universes are independent, and the exchanges
need not be invertible. Existing `TwoSquare` pasting supplies its coefficient
relations. The small-etale chart and unit section families consume this same
constructor; the component views retain their original factors.

## Whole composition cubes

`CompositionCube` and `CompositionCubeWhole` normalize the actual functor
composition comparisons on a complete cube before taking components. They
are used by the scalar-forgetting derived mate cube; `CompositionSquare`
retains the corresponding original two-dimensional equations.

[NatTrans/UnitInsertion](NatTrans/UnitInsertion.lean) constructs the complete
transformation inserting an original target unit into the same functor
composite. Its whole-value and component equations retain the two original
factors. The Godement pullback-pushforward unit is a current consumer.

[ComparisonPasting/ExchangeInterchange](ComparisonPasting/ExchangeInterchange.lean)
proves the complete noninvertible exchange rectangle from its original
pastings, equality transports and comparison isomorphisms. Relative etale
chart exchange uses this whole argument before evaluating components.
[ComparisonPasting/LocalizationVertices](ComparisonPasting/LocalizationVertices.lean)
constructs the whole natural isomorphism from two original localization
factors and proves its unit and counit values. Bounded-below and unbounded
localization specialize it separately, retaining their own categories and
original connecting maps.

## Additional source entry points

- [CartesianImageNaturality](CartesianImageNaturality.lean)
- [ChosenImageComparison](ChosenImageComparison.lean)
- [ChosenLeftUnit](ChosenLeftUnit.lean)
- [ChosenRightUnit](ChosenRightUnit.lean)
- [CompositionAssociativityTransfer](CompositionAssociativityTransfer.lean)
- [CompositionChoice](CompositionChoice.lean)
- [CompositionExchangeIso](CompositionExchangeIso.lean)
- [CompositionExchangeTransport](CompositionExchangeTransport.lean)
- [CompositionFamilySquare](CompositionFamilySquare.lean)
- [CompositionIdentityNormalization](CompositionIdentityNormalization.lean)
- [CompositionIsoNaturality](CompositionIsoNaturality.lean)
- [CompositionToTargetTransport](CompositionToTargetTransport.lean)
- [FaithfulComposition](FaithfulComposition.lean)
- [IdentitySourceExpansion](IdentitySourceExpansion.lean)
- [IdentitySourceRestriction](IdentitySourceRestriction.lean)
- [ImageCartesianCompositionIso](ImageCartesianCompositionIso.lean)
- [ImageCartesianComposition](ImageCartesianComposition.lean)
- [ImageComparisonRestrictionCongruence](ImageComparisonRestrictionCongruence.lean)
- [ImageComparisonRestriction](ImageComparisonRestriction.lean)
- [ImageCompositionAssembly](ImageCompositionAssembly.lean)
- [ImageCompositionExchangeActual](ImageCompositionExchangeActual.lean)
- [ImageCompositionExchangeFaces](ImageCompositionExchangeFaces.lean)
- [ImageCompositionExchangeRestriction](ImageCompositionExchangeRestriction.lean)
- [ImageCompositionExchange](ImageCompositionExchange.lean)
- [ImageCompositionIsoFormula](ImageCompositionIsoFormula.lean)
- [ImageCompositionMap](ImageCompositionMap.lean)
- [ImageCompositionPrewhisker](ImageCompositionPrewhisker.lean)
- [ImageCompositionRefinement](ImageCompositionRefinement.lean)
- [ImageCompositionRestriction](ImageCompositionRestriction.lean)
- [ImageCompositionTarget](ImageCompositionTarget.lean)
- [ImageCompositionToTargetAmbient](ImageCompositionToTargetAmbient.lean)
- [ImageCompositionToTargetComponents](ImageCompositionToTargetComponents.lean)
- [ImageCompositionToTargetFaces](ImageCompositionToTargetFaces.lean)
- [ImageCompositionToTargetRestriction](ImageCompositionToTargetRestriction.lean)
- [ImageCompositionToTarget](ImageCompositionToTarget.lean)
- [ImageCompositionTransport](ImageCompositionTransport.lean)
- [ImageFirstRefinement](ImageFirstRefinement.lean)
- [ImageFirstTargetRefinement](ImageFirstTargetRefinement.lean)
- [ImageIdentityContraction](ImageIdentityContraction.lean)
- [ImageInterchangeAssembly](ImageInterchangeAssembly.lean)
- [ImageInterchangeAssociativity](ImageInterchangeAssociativity.lean)
- [ImageInterchangeHorizontal](ImageInterchangeHorizontal.lean)
- [ImageLeftRoute](ImageLeftRoute.lean)
- [ImageLeftUnitAssembly](ImageLeftUnitAssembly.lean)
- [ImageLeftUnitEquation](ImageLeftUnitEquation.lean)
- [ImageRightOpenTransport](ImageRightOpenTransport.lean)
- [ImageRightRealization](ImageRightRealization.lean)
- [ImageRightRoute](ImageRightRoute.lean)
- [ImageRightUnitComparison](ImageRightUnitComparison.lean)
- [ImageRightUnitIdentity](ImageRightUnitIdentity.lean)
- [ImageRightUnitMiddle](ImageRightUnitMiddle.lean)
- [ImageRightUnitOpen](ImageRightUnitOpen.lean)
- [ImageRightUnitRestriction](ImageRightUnitRestriction.lean)
- [ImageRightUnitStructural](ImageRightUnitStructural.lean)
- [ImageRightUnit](ImageRightUnit.lean)
- [ImageSourceIdentity](ImageSourceIdentity.lean)
- [ImageStructuralRectangle](ImageStructuralRectangle.lean)
- [ImageTargetRefinement](ImageTargetRefinement.lean)
- [ImageTripleCompositionPredicate](ImageTripleCompositionPredicate.lean)
- [ImageTripleComposition](ImageTripleComposition.lean)
- [ImageUnitCompositionFormula](ImageUnitCompositionFormula.lean)
- [ImageUnitHorizontal](ImageUnitHorizontal.lean)
- [ImageUnitRestriction](ImageUnitRestriction.lean)
- [IsoSquarePostcompose](IsoSquarePostcompose.lean)
- [OpenCompositionCoherence](OpenCompositionCoherence.lean)
- [OpenCompositionPost](OpenCompositionPost.lean)
- [RightUnitOfAssociativity](RightUnitOfAssociativity.lean)
- [TargetExchangeNormalization](TargetExchangeNormalization.lean)
- [TargetExchangePostcomp](TargetExchangePostcomp.lean)
- [TargetIdentityExchange](TargetIdentityExchange.lean)
- [TargetUnitSquare](TargetUnitSquare.lean)

[OriginalComparisonIdentities](OriginalComparisonIdentities.lean) gives
whole reflexivity, composition and identity-normalization equations for
the original functors and comparison isomorphisms in variable categories.
Its double-contravariant identity laws use the same supplied functor twice.
These categorical equations precede their module-bidual and geometric
specializations and add no mathematical object or replacement comparison.
