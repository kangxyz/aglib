# Proper prefixes and the original unchanged open

Source: [SupportedStages.lean](SupportedStages.lean).

This leaf uses the native stages of the given `NormalizedPointBlowupChain`.
It constructs neither a second chain nor a supplied compatibility tower.

`isProper_toBase_and_fromTop` assumes only local Noetherianity of the original
base and properness of the actual total map. The existing first-step/tail
properness theorem and proper composition prove both factors at each cut proper.
The refl case needs no integrality; each cons stores the integrality required
by the native normalization theorem. No global Nagata premise is introduced.

`isIso_toBase_restrict` additionally assumes an integral original base and an
actual nonempty open U on which the total map is an isomorphism. It uses exactly
`inv (f | U)`, the original open inclusion and the original suffix arrow to
construct the dominant section of the prefix. Nonemptiness of the inverse-image
open is witnessed by the image of an actual point under that inverse; density
then follows in the original integral terminal. The prefix is separated because
it is proper, so the existing dominant-section theorem supplies its inverse.
The same nonempty-open argument also makes U dense in the integral original
base and its inclusion dominant; no empty-open dominance assertion is used.

For the intended point complement, nonemptiness is supplied by the original
generic point and the original closed nongeneric-centre hypothesis, not by a
new final assumption. The theorem itself applies to any genuine nonempty open.

No dimension, normality, canonical coefficient, cohomology, rationality,
ordinary-stage normality or resolving-chain existence is asserted here.
Local pullbacks, their field maps and dimension transport remain the next
separately reviewed packet.

Direct consumers: [AlgebraicGeometry/Surfaces/Resolution/NormalizedPointBlowupChain/LocalStages](LocalStages.md), [AlgebraicGeometry/Surfaces/Resolution/NormalizedPointBlowupChain/ProjectiveStages](ProjectiveStages.md).
