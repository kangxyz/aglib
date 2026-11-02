# Local-spectrum normalization of ordinary direct images

Source: [Localization.lean](Localization.lean).

For qcqs `h : Y → X` and quasicoherent `M`,
`Localization.lean` constructs the original scalar-linear comparison

`mu : (h_*M)_x ≃ Γ(Y ×_X Spec O_(X,x), a* M)`.

Its factors are the original `rightDerivedZeroIsoSelf` inverse, the
native flat-base-change higher-image stalk comparison in degree zero
and the original H0/sections equivalence.
For an actual `tau : h_*M → N`, the localized section map is
`rho = tau_x ∘ mu.inverse`, with `rho(mu(s))=tau_x(s)`.
An equivalence for `rho` requires invertibility of that same `tau`.

[LocalEvaluation](LocalEvaluation.md) and
[AffineEvaluation](AffineEvaluation.md) identify these maps with the
ordinary base-change mate and geometric counit, retaining the actual
pullback and inverse coefficient map.

The canonical-stalk Ext and dimension comparisons are publicly imported
from [CanonicalStalk](../CanonicalStalk.md). They retain the original
affine quotient, ambient coefficient, embedding degree and global
open-stalk scalar map. Ambient dimension is embedding degree plus actual
source-stalk dimension. The local normalization shift is that source
dimension, rather than a uniform two. No later stalk is assumed finite
or complete over the original regular base.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/Trace/LocalEvaluation](LocalEvaluation.md).
