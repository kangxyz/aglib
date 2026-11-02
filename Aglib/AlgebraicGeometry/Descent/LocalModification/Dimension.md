# Dimension through the same supported local square

Source: [Dimension.lean](Dimension.lean).

`topologicalKrullDim_le_of_local_replacement` uses an actual square along
X.fromSpecStalk x for a closed x, an isomorphism over its actual complement,
and dimension bounds d on X and the original local source T. It bounds the
same global source Y by d, for arbitrary d:WithBot ℕ∞.

This is the single stalkwise body extracted from ProjectiveSurfaceChain.
Over x, the original point lift and actual localization projection identify
stalks with T. Away from x, the actual morphismRestrictStalkMap identifies
them with X. No integrality, normality, properness, Noetherianity, Nagata,
catenarity or finite-parent hypothesis is used. The original projective
consumer is a thin caller at d=2 with its public statement unchanged.

LocalStages first derives the literal local model's dimension through
original birational affine charts, then invokes this transport. It does
not supply per-stage dimension as a new conclusion-oracle premise.

Direct consumers: [AlgebraicGeometry/Descent/LocalModification/ProjectiveSurfaceChain](ProjectiveSurfaceChain.md), [AlgebraicGeometry/Surfaces/Resolution/NormalizedPointBlowupChain/LocalStages](../../Surfaces/Resolution/NormalizedPointBlowupChain/LocalStages.md).
