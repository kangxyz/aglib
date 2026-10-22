# Finite-presentation module maps and properties

The diagram is an actual cofiltered system of schemes with affine transition
maps and a specified limiting cone. Coefficient sheaves use the native finite
presentation predicate and the original pullback functors.

[Affine](Affine.lean) constructs finite presentation of the actual affine
section modules and the native affine comparisons. [Maps](Maps.md) proves
global Hom descent on qcqs stages and eventual equality on quasi-compact
stages. Both supplied coefficient sheaves remain finitely presented. The
fixed-base Hom theorem retains the original structural triangles.

[Properties](Properties.md) descends invertibility of the given stage arrow,
a specified isomorphism with both hom/inverse recovery equations, and local
rank one of the given stage coefficient. Rank-one descent constructs genuine
finite affine covers and their original frames. Every conclusion concerns an
actual later pullback of the supplied coefficient or arrow.

The comparisons are the original `pullbackConeCompIso` and
`pullbackHomOfTriangle`, with literal recovery equations. No Noetherianity,
coherence, flatness, injective transitions or supplied model family is assumed.
The public scheme and index universes are the displayed common universe.

Global module-object and finite-diagram effectivity remain separate
obligations. The [finite matrix suppliers](../../../../Algebra/Category/ModuleCat/Descent/FinitePresentation/README.md)
belong to algebraic module descent, and the sibling scheme-object theorems
belong to the [parent family](../README.md).
