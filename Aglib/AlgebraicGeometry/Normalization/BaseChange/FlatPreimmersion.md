# Normalization under a flat preimmersion

Source: [FlatPreimmersion.lean](FlatPreimmersion.lean).

`Scheme.Hom.normalizationPullback_isIso_of_flat_preimmersion` assumes a qcqs
original morphism `f : X ⟶ S` and a flat preimmersion `g : Y ⟶ S`.
It concludes invertibility of the native comparison `f.normalizationPullback g`.
There is no Noetherian, normality, dimension, excellence or algebraization
premise. Crucially, this is not a theorem for arbitrary flat `g`.

Flatness and preimmersion identify the original stalk maps of `g` as
isomorphisms. At each `y : Y`, the naturality square expresses the composite
from its stalk spectrum as the corresponding original target stalk map
precomposed with `Spec.map (g.stalkMap y)`. The own-stalk normalization
comparison and the native isomorphism-base-change comparison therefore give
invertibility for this composite. The actual comparison-pasting equation
then gives invertibility of the first comparison after the base change to
that local spectrum.

The normalization comparison itself is integral, hence closed. The general
`StalkDetection` theorem now proves it is an isomorphism by testing these
actual base stalks. A model obtained by base change from an original stalk
map fits this flat-preimmersion hypothesis; it is never asserted to be a
single stalk spectrum of the model.

Both original equations `normalizationPullback_snd` and
`toNormalization_normalizationPullback_fst` apply unchanged to this same
comparison. The further generic-source and normalized-point-chain transports
are separate consumers.

Direct consumers: [AlgebraicGeometry/Normalization/FunctionField/FlatPreimmersion](../FunctionField/FlatPreimmersion.md).
