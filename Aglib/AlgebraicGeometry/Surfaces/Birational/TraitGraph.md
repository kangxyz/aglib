# The actual common graph over a trait

Import `Aglib.AlgebraicGeometry.Surfaces.Birational.TraitGraph`.

`Scheme.TraitGraph.model R F f g e` is the native scheme-theoretic closure
of the graph of the specified isomorphism `e` in `Over (Spec (.of F))`
between the literal generic fibres of the original structural maps `f`
and `g`. The base is the
original domain DVR `R`, with its supplied fraction field `F` and original
fraction-ring algebra map. The existing DVR localization theorem makes
that exact map an open immersion.

The original projections are `toSource` and `toTarget`; their structural
composites agree. `sourceGenericIso` and `targetGenericIso` identify the
literal generic fibre of the common model with the two original generic
fibres. Their forward maps are the native base changes of those original
projections, and their relation is exactly the supplied `e`.

For an integral Noetherian source with proper flat structural map and a
proper target structural map, the actual graph model is integral,
Noetherian, proper and flat over `R`. Its source projection is proper and
surjective. If the target is integral, its target projection is also
proper and surjective. The construction needs no regularity, dimension
or excellence premise. A separate flatness premise on the target is
unnecessary for these conclusions. The individual `toSource_surjective`
instance does not require source Noetherianity. The individual
`toTarget_dominant` and `toTarget_surjective` instances require neither
source Noetherianity nor properness of the target structural map.

The flatness proof uses injectivity of the actual stalk maps of an
integral dominant morphism to the Dedekind base. The resulting stalk
modules are torsion-free, hence flat by the native Dedekind-domain
criterion.

`liftSection` takes the two supplied sections, their original section
equations, and equality of their literal generic sections under `e`.
It factors their paired map through the actual closed graph by ideal
kernel containment and schematic density of `Spec F ⟶ Spec R`.
`liftSection_toSource`, `liftSection_toTarget`, and `liftSection_toBase`
retain both original section triangles and the section equation.

`sourceFunctionFieldEquiv` and `targetFunctionFieldEquiv` are isomorphisms
from the two original function fields to that of the actual graph model.
Their forward homomorphisms are the function-field maps of the original
projections, as recorded by the corresponding `_apply` lemmas. They follow
from functoriality and the function-field isomorphisms of the actual open
graph and its two open projections.

This is a common proper integral flat graph model. It does not supply
a regular common model or a resolution theorem.
