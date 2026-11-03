# Detecting isomorphisms on local-spectrum base changes

Source: [StalkBaseChange.lean](StalkBaseChange.lean).

`Scheme.isIso_of_isClosedMap_of_stalkPullback` assumes that the original
scheme map is closed and that its literal base-change projection over every
actual target stalk is invertible. It concludes that the map is an
isomorphism. Surjectivity and injectivity are proved by lifting points over
the original closed points of those local spectra. Closedness then gives a
homeomorphism. The actual stalk-map arrow is transported through flat
localization, proving the remaining ringed-space condition.

`isIso_of_isClosedMap_of_baseStalkPullback` tests the actual stalk spectra of
an arbitrary original base instead. The model-localization projection is
retained literally. Each target stalk factors through the model localization
using `Spec.map` of the original structural stalk map and its naturality
square. It is not identified with the entire model localization.

`isPullback_overBaseChange` and `isIso_pullback_snd_of_overBaseChange` relate
the original map of two base-changed models to the literal structural
base-change projection, with the supplied original structural equality.
These are ordinary cartesian-square and isomorphism-detection results;
no normality, finite-presentation or algebraization claim is assumed.

The intended consumer is the integral native normalization comparison;
its integral morphism supplies the required closedness.

Direct consumers: [AlgebraicGeometry/Normalization/BaseChange/FlatPreimmersion](../../Normalization/BaseChange/FlatPreimmersion.md).
