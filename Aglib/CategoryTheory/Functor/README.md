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
