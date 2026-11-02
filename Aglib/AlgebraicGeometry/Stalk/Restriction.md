# Original stalk maps on an isomorphism open

Source: [Restriction.lean](Restriction.lean).

Import `Aglib.AlgebraicGeometry.Stalk.Restriction`.
The namespace is `AlgebraicGeometry.Scheme.Hom`.

`isIso_stalkMap_of_isIso_morphismRestrict` takes an arbitrary scheme morphism
`f : Y -> X`, an actual target open `U`, a genuine `IsIso (f|U)`, and an
original point `y` with `f y` in `U`. It proves `IsIso (f.stalkMap y)` for
that ORIGINAL stalk homomorphism.

The point in the original preimage open and native restriction Cartesian
square determine the original stalk-arrow isomorphism. Its arrow-isomorphism
property transfers the known restricted stalk isomorphism. No new stalk,
localization, scalar map or geometric comparison is selected.

This is the generic final calculation factored once from
`Resolution/Principalization.pointBlowup_stalkMap_isIso_of_ne`. The old public
point-blowup statement and original complement proof remain, with only that
calculation replaced by a call. No Noetherianity, flatness of f, normality,
regularity, dimension, dominance or point-closedness is required here.

Direct consumers: [AlgebraicGeometry/Surfaces/Resolution/NormalizedPointBlowupChain/SingularAncestors](../Surfaces/Resolution/NormalizedPointBlowupChain/SingularAncestors.md), [AlgebraicGeometry/Surfaces/Resolution/Principalization](../Surfaces/Resolution/Principalization.md).
