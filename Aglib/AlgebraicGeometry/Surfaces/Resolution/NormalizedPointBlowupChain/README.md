# Actual stages of a supplied normalized-point chain

[Stages](Stages.lean) exposes the existing chain's native cuts, centres,
prefixes and suffixes with their exact maps and lengths.
[SupportedStages](SupportedStages.lean) derives properness of both factors
from properness of the actual total map over a locally Noetherian base.
It retains the original unchanged nonempty open; the bare datatype does
not imply properness.

[ProjectiveEmbedding](ProjectiveEmbedding.lean) constructs a finite
projective embedding of the same terminal from a supplied embedding of
the integral locally Noetherian base and properness of the total map.
[FiniteBaseEmbedding](FiniteBaseEmbedding.lean) starts instead with an
actual finite base map. No Noetherianity of its coefficient ring is added.
[ProjectiveStages](ProjectiveStages.lean) retains interior embeddings and
generic-image triangles over a domain with the stated dominant and finite
generic-image maps.

[LocalStages](LocalStages.lean) uses the original supported proper chain
over an integral locally Noetherian surface and a Nagata original stalk;
its local models are literal target-stalk pullbacks.
[OrdinaryStages](OrdinaryStages.lean),
[SingularAncestors](SingularAncestors.lean) and
[StepDerivedUnit](StepDerivedUnit.lean) additionally retain normality,
dimension at most two, an original closed nongeneric rational Nagata
dimension-two stalk and the actual support isomorphism.
They derive whole ordinary-stage normality, normalization isomorphisms,
singular-ancestor geometry and original step-unit invertibility from
those data. Future stage properties are not supplied independently.

Present consumers include [Supported globalization of a prescribed local modification](../../../Descent/LocalModification/README.md).
