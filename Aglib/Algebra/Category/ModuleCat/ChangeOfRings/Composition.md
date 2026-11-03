# Native scalar-triangle comparison laws

Source: [Composition.lean](Composition.lean).

The equality-transported native `ModuleCat.extendScalarsComp` retains its original
unit-tensor value and reflexive component. These laws use the actual native
isomorphism expression, with its original ring maps, equality direction and
universe. They introduce no second comparison constructor.

The existing `Descent/FinitePresentation/Maps` provider and its public
`extendScalarsCompOfEq` API retain their original source. General pushout
comparisons use this focused leaf without importing matrix descent.
