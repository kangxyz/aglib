# Generic normalization along dominant flat preimmersions

Source: [FlatPreimmersion.lean](FlatPreimmersion.lean).

`genericNormalizationPullbackIso` assumes actual integral schemes and a
dominant flat preimmersion between them. It identifies the normalization of
the original upper generic inclusion with the literal pullback of the lower
normalization. The source fields are compared by `Spec.map` of the original
`Scheme.functionFieldMap`, proved invertible from the actual generic stalk
map; an abstract field equivalence is not substituted.

`genericPoint_isPullback_of_flat_preimmersion` constructs the original generic
cartesian square. The normalization source transport then feeds the proved
native normalization-pullback comparison. Both equations are exported:
`genericNormalizationPullbackIso_hom_snd` retains the normalization arrow,
and `toNormalization_genericNormalizationPullbackIso_hom_fst` retains the
original function-field arrow and the original `toNormalization` maps.

No normalization finiteness, properness, Noetherianness or resolution
assumption is used here. Those are separate obligations of the global-chain
consumer.

Direct consumers: [AlgebraicGeometry/Descent/LocalModification/NormalizationAway](../../Descent/LocalModification/NormalizationAway.md), [AlgebraicGeometry/Descent/LocalModification/NormalizedPointLocalization](../../Descent/LocalModification/NormalizedPointLocalization.md), [AlgebraicGeometry/Surfaces/RationalSingularities/RegularTarget](../../Surfaces/RationalSingularities/RegularTarget.md).
