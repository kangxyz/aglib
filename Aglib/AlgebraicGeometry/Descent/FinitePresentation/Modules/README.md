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

[Objects](Objects.md) supplies `Scheme.Modules.exists_model_above_of_isLimit`:
any finitely presented module on the limit has a finitely presented model
above any prescribed stage, with a native isomorphism after pullback by the
original cone projection. Its given-model and filtered-ring-colimit forms
use the literal canonical scheme base changes of a qcqs model.

[Diagrams](Diagrams.md) supplies `Scheme.Modules.exists_functor_above_of_isLimit`
for a functor from a native finite category with finitely presented objects.
It returns an actual later-stage functor and a natural isomorphism after the
original projection pullback. `exists_iso_above_of_isLimit` descends a specified
isomorphism together with models of its endpoints, retaining both its original
hom and inverse equations. The given-model specialization uses the same
canonical base-change diagram.

The comparisons are the original `pullbackConeCompIso` and
`pullbackHomOfTriangle`, with literal recovery equations. No Noetherianity,
coherence, flatness, injective transitions or supplied model family is assumed.
The scheme diagram and its index use the displayed common universe; the
finite diagram category may have an independent universe.

The [finite matrix suppliers](../../../../Algebra/Category/ModuleCat/Descent/FinitePresentation/README.md)
belong to algebraic module descent, and the sibling scheme-object theorems
belong to the [parent family](../README.md).
