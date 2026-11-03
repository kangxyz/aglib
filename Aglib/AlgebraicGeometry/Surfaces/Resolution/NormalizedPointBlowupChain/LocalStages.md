# Literal target-stalk pullbacks of the original supported prefixes

Source: [LocalStages.lean](LocalStages.lean).

`localStage_geometry` starts with the given proper normalized-point chain
c:f:Z→X, integral locally Noetherian X of dimension at most two, an original
closed nongeneric x, original total restriction iso off x, and genuine
Nagata of the ONE original stalk S=X.stalk x. An index selects only the
native prefix already stored in c.

The local scheme is literally Pi=pullback (c.toBase i) (X.fromSpecStalk x),
with its native first and second projections ai/pi. No replacement or chosen
model is introduced. The result retains actual integrality/dominance proofs,
proper prefix and suffix, local Noetherianity of Xi, proper pi, original
prefix support, the total and Cartesian structural triangles, all original
field maps and their exact commuting square.

Properness is derived from the proper total chain. The prefix is genuinely
surjective by proper dominance; thus the literal second projection is also
surjective/dominant. This does not assert arbitrary base-change stability
of dominance. ModelLocalization derives integrality and first-projection
dominance; flat preimmersion gives its actual field isomorphism. Original
field-square cancellation derives the local structural field isomorphism.

The original stalk dimension bound follows from dim X≤2. The small actual
ΓSpecIso/identity-chart supplier and existing birational adapted charts
then derive dim Pi≤2. Actual central/away stalk isomorphisms give dim Xi≤2.
There is no per-stage dimension input and no cohomological dimension proof.

No global Nagata assumption, parent-finite map, completion, later-stalk
Nagata/rationality, normal ordinary stage, normalization iso, embedding,
canonical comparison or generation claim occurs here. Those later producer
obligations remain separate.

Direct consumers: [AlgebraicGeometry/Surfaces/Resolution/NormalizedPointBlowupChain/OrdinaryStages](OrdinaryStages.md).
