# Properness of prescribed steps from the actual proper total map

Source: [ChainProperness.lean](ChainProperness.lean).

`firstNormalization_isFinite_of_proper_chain` starts with an integral locally
Noetherian scheme, a closed nongeneric centre, the actual native normalized
point-step tail, and **properness of the actual composite total map**. It
concludes finiteness of the literal first generic normalization.

The actual terminal factor through the ordinary first blowup is proper
because its composite is proper and the ordinary blowup is separated. The
native chain supplies its integral normal source and original function-field
isomorphism. The existing proper-birational normalization theorem then
forces finiteness. No property is inferred just from membership in the chain
datatype, and there is no finiteness, excellence or Nagata premise.

Direct consumers: [AlgebraicGeometry/Surfaces/Resolution/NormalizedPointBlowupChain/ProjectiveEmbedding](../../Surfaces/Resolution/NormalizedPointBlowupChain/ProjectiveEmbedding.md), [AlgebraicGeometry/Surfaces/Resolution/NormalizedPointBlowupChain/SupportedStages](../../Surfaces/Resolution/NormalizedPointBlowupChain/SupportedStages.md).
