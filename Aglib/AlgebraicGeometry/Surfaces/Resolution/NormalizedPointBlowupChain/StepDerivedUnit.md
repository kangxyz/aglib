# Derived units of the actual ordinary and normalization steps

Source: [StepDerivedUnit.lean](StepDerivedUnit.lean).

Import `Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain.StepDerivedUnit`.
The namespace is `AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain`.

`isIso_moduleDerivedPushforwardUnit_ordinaryDatum_and_normalizationMap`
uses the SAME proper supported normalized-point chain, integral locally
Noetherian normal surface X, actual closed nongeneric x, original support
isomorphism, and genuine Nagata/rational dimension-two stalk at x.
It derives invertibility of the original derived structure unit of the
actual ordinary blowdown and of the literal normalization arrow at each
native step. It assumes no per-stage unit or centre rationality.

The ordinary source dimension is derived from the same next native stage
through its actual normalization isomorphism. At a dimension-two centre
over x, the accepted actual localized-model rationality supplier gives
Nagata and rationality of that centre, and the original point-blowup unit
supplier applies. Otherwise the accepted single ordinary-stage classification
gives invertibility of the actual blowdown itself.

For an actual isomorphism, existing affine direct-image acyclicity kills R1
of the original unit coefficient. The existing surface derived-unit theorem
then applies with the original generic-stalk field map. The same argument
handles the literal normalization arrow. No pushforward cancellation,
new derived category, coefficient comparison or substitute morphism is used.

This pair concerns the two actual arrows whose composite is c.step j by the
existing normalizationMap_comp law. It does not silently replace the
normalized step by its ordinary blowdown. No prefix-unit wrapper is included:
Supported remains available directly when a future consumer needs it.
No embedding, canonical trace, generation, canonical-pullback epimorphism,
frame or Gorensteinness is claimed.
