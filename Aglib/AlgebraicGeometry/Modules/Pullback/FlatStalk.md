# Original stalk detection under flat pullback

Source: [FlatStalk.lean](FlatStalk.lean).

Import: `Aglib.AlgebraicGeometry.Modules.Pullback.FlatStalk`.

`Scheme.Modules.moduleStalk_zero_iff` identifies vanishing of the original
module-valued and additive stalks. `Scheme.Modules.stalk_isZero_of_flat_pullback`
uses the original stalk map, its native flat local algebra, and the original
pullback-stalk comparison to infer vanishing at the image of an actual point
from vanishing of the actual flat pullback. No finiteness, quasicoherence,
Noetherianity or global surjectivity is required.

The two existing proof bodies move unchanged from
`Modules/Coherent/Support/FinitePushforward`. That owner keeps its original
public names as thin wrappers, so no second proof or alternative stalk model
is introduced.

The lower imports consist of the actual `Pullback/FlatMorphism` provider,
native faithful-flat algebra, and the algebraize tactic. Static Aglib import
closure contains neither coherent-category nor SmallModel owners.

Direct consumers: [AlgebraicGeometry/Modules/Coherent/Support/FinitePushforward](../Coherent/Support/FinitePushforward.lean), [AlgebraicGeometry/Modules/Locality/PointLocalization](../Locality/PointLocalization.md).
