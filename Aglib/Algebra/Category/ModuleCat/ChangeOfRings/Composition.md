# Original scalar-triangle comparison

Source: [Composition.lean](Composition.lean).

`extendScalarsCompOfEq` and `extendScalarsCompOfEq_hom_app_one_tmul` are the
original two declarations moved unchanged from Descent/FinitePresentation/Maps.
Their global ModuleCat names, uniform universe, ring-map inputs, equality
direction, native whole-functor equality transport, associator and unit values
are preserved. The former owner publicly imports this leaf and contains no
second implementation or alias wrapper.

The concrete consumers are the existing finite matrix-cokernel descent maps
and the original regular-source pushout comparison. This avoids making general
scalar composition depend on matrix descent.

The reflexive component equation for the original extendScalarsCompOfEq is proved once beside its existing constructor, retaining the same native extendScalarsComp component.

Direct consumers: [Algebra/Category/ModuleCat/ChangeOfRings/Pushout](Pushout.md), [Algebra/Category/ModuleCat/Descent/FinitePresentation/Maps](../Descent/FinitePresentation/Maps.lean).
