# Projective embeddings of the original proper normalized-point chain

Source: [ProjectiveEmbedding.lean](ProjectiveEmbedding.lean).

`Blowup.NormalizedPointBlowupChain.exists_projective_embedding` embeds the SAME
terminal scheme of a supplied proper normalized closed-point chain into finite
positive standard projective coordinates. Its equation retains the original
chain map followed by the given base embedding and its structural morphism.

The coefficient ring R is arbitrary and commutative. The chain base X is
integral and locally Noetherian and has a supplied closed immersion into a
finite-coordinate projective space over R. Properness is assumed for the actual
total chain map; the bare chain datatype does not imply properness. No
Noetherianity of R, dimension bound, Nagata hypothesis, normality of X or
regularity of the terminal is assumed.

The proof inducts on the existing chain. In a nonempty step, `ChainProperness`
derives finiteness of the literal first generic normalization and properness of
the actual tail. The one original-blowup embedding body now belongs to
[OriginalEmbedding](../../../Blowup/ProjectivePresentation/OriginalEmbedding.md).
Its unchanged identity-base-change projection comparison gives the embedding
of the ORIGINAL ordinary blowup and its exact structure equation. The original
normalization followed by that embedding is finite, so the existing finite-map
projective embedding applies. The induction
then continues on the same proper tail, with locally Noetherian base derived
from the actual proper first step. The original structure triangles compose.

The empty chain uses the same finite-map embedding theorem on the given closed
base embedding. Nonempty coordinates are derived from the actual integral
source, not assumed. No replacement terminal, normalized-to-ordinary object
equality, regularity theorem or resolution construction is introduced.

This dimension-free interface belongs to the existing normalized-chain family.
Its later affine starting specialization can use `ProjectiveSpace.pointIsoSpec`.
The leaf itself does not construct canonical frames, prove regularity of a
normal terminal or complete the resolution existence argument.

Direct consumers: [AlgebraicGeometry/Descent/LocalModification/ProjectiveSurfaceChain](../../../Descent/LocalModification/ProjectiveSurfaceChain.md), [AlgebraicGeometry/Surfaces/Resolution/NormalizedPointBlowupChain/ProjectiveStages](ProjectiveStages.md).
