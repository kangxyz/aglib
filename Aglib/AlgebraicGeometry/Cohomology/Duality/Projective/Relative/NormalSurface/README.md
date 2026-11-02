# Canonical coefficients on embedded normal surfaces

The common surface data are an integral scheme with normal stalks and
dimension at most two, a closed embedding in finite-coordinate projective
space over a regular local domain, a dominant structural map and finite
original generic-image base map. The canonical module is the original
chosen-embedding homology; later stalks are not assumed complete or finite
over that regular base.

[CanonicalStalk](CanonicalStalk.lean) and
[StalkGorenstein](StalkGorenstein.lean) retain the actual quotient and
open-stalk maps. Finite native self-injective dimension of an original
stalk is equivalent to a linear frame of its original canonical stalk.
[GenericFrame](GenericFrame.lean) chooses one such frame at the original
generic point. [StalkEmbedding](StalkEmbedding.lean) uses that same choice
for every germ and embeds the finite torsion-free canonical stalk into
the original function field, with its actual fractional numerator.

[LocalIdeal](LocalIdeal.lean) identifies the pulled global canonical
coefficient with the ideal module of that numerator.
[LocalImage](LocalImage.lean) constructs its quotient onto the actual ideal
image on an arbitrary local model. The rank-one image and the target's own
canonical stalk are compared by
[LocalImageFrame](LocalImageFrame.lean) only with the supplied derived
structure-unit isomorphism and actual inverse-trace stalk surjectivity.

[CartierRegularity](CartierRegularity.lean) proves scalar regularity and
Cartier-section monicity on the original canonical module.
[CartierRestriction](CartierRestriction.lean) identifies its restriction
to the full Cartier curve with the coefficient canonical sheaf tensored
with the restricted ideal. That comparison retains a dimension-two
regular local base, its original finite local residue map, the positive
curve embedding and the actual derived residue coefficient line.

[ExceptionalCoefficientVanishing](ExceptionalCoefficientVanishing.lean)
and [LocalizedExceptionalCanonicalVanishing](LocalizedExceptionalCanonicalVanishing.lean)
use the stated rational blowup, coefficient restriction and Cartier
monicity to descend the original vanishing and section-lifting results.
They do not establish all-model structure-H1 vanishing or a global trace
theorem. The [trace family](Trace/README.md) keeps its additional inputs
visible.

Present consumers include [Original canonical trace and local evaluation](Trace/README.md), [The original normal-surface canonical restriction](CartierRestriction.md).
