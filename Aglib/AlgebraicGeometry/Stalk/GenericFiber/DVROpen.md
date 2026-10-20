# Actual generic-fibre projection geometry

[DVROpen](DVROpen.lean) proves
`Scheme.LocalRing.GenericFiber.baseMap_isOpenImmersion` for the actual
fraction-field algebra map of any domain DVR. It identifies the supplied
fraction field with localization away from an irreducible uniformizer.
The field, algebra and `IsFractionRing` instances are the original inputs;
there is no characteristic, completion or finiteness premise.

The lower [GenericFiber](../GenericFiber.lean) owns `baseMap`, the literal
pullback `scheme`, its `projection` and the actual projection-stalk equivalence.
The function-field consumer is
[DedekindGenericFiber](../../FunctionField/DedekindGenericFiber.lean).

The source is `FunctionField/DVRGenericOpen.lean` under
`R5Lab/Aglib/AlgebraicGeometry`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`; its complete SHA-256 is in the
module header. The source theorem `genericBase_open` is the native
`baseMap_isOpenImmersion` theorem on exactly the same map.
