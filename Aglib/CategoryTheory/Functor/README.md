# Native functors and their comparisons

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
