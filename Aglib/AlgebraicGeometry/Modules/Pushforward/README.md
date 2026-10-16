# Actual direct-image comparisons

[Isomorphism](Isomorphism.lean), imported as `Aglib.AlgebraicGeometry.Modules.Pushforward.Isomorphism`, gives `Scheme.Modules.pushforwardIsoRestrict`: direct image along an actual scheme isomorphism agrees naturally with restriction along its inverse, including the section components.

Canonical direct image is Mathlib's scalar-restricted module-sheaf functor. Its affine comparison with actual restriction of scalars belongs to [quasicoherent affine theory](../QuasiCoherent/Affine/README.md). [The canonical finite-type direct-image implementation](../QuasiCoherent/FiniteType/Pushforward.lean) uses the same native sheaf pushforward; affine/closed/ideal interfaces are transparent specializations. Their guarded coherent and exact layers keep source/target local Noetherianity. [Base change](../BaseChange/README.md) identifies its adjunction mate rather than choosing a replacement functor.

[Stalk](Stalk.lean), [ClosedImmersion](ClosedImmersion.lean) and [SectionStalk](SectionStalk.lean) compare actual direct-image stalks and sections, with the specified closed-immersion or section/stalk hypotheses of each result. These lie below coherent interpretation and feed projection-formula and Godement comparisons.

[ClosedImmersion/Colimits](ClosedImmersion/Colimits.lean) extends this actual
pushforward to arbitrary small colimits of all module sheaves. The original
stalk comparisons and off-image zero stalks give the proof; this is the
ordinary right-adjoint existence input for closed-immersion duality.
