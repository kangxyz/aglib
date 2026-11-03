# Relative normalization under affine localization

Source: [AffineLocalization.lean](AffineLocalization.lean).

`Scheme.Hom.normalizationPullback_isIso_of_affineLocalization` concerns the
native comparison `f.normalizationPullback g`. It assumes qcqs `f : X ⟶ S`,
a flat morphism `g : Y ⟶ S` between affine schemes, and a multiplicative set
`M` of `Γ(S, ⊤)` for which `Γ(Y, ⊤)` is a localization. That localization uses
the algebra structure of the actual map `g.appLE ⊤ ⊤`; it is not an abstract
isomorphism of unrelated rings.

The proof adapts Andrew Yang's affine calculation in the pinned Mathlib
`AlgebraicGeometry/Normalization.lean`, lines 602–682. The two actual
flat section-pushout comparisons and all equations are retained; the ring
input is `TensorProduct.toIntegralClosure_bijective_of_isLocalization`
from `RingTheory/Smooth/IntegralClosure.lean`, rather than its smooth
specialization. The comparison is consequently the original morphism, and
its existing `normalizationPullback_snd` and
`toNormalization_normalizationPullback_fst` equations remain applicable.

The downstream `StalkNormalization` leaf derives the localization premise
for an affine base's original stalk. Neither this lemma nor that
specialization asserts normalization compatibility with arbitrary flat
base change.

Direct consumers: [AlgebraicGeometry/Normalization/BaseChange/Stalk](Stalk.md).
