# Literal stalk pullbacks of generic normalization

`LocalPullback.lean` constructs the stalk pullback of the existing native relative
normalization. Its current consumers are `NormalCurve.lean` and the morphism leaf
`Aglib.AlgebraicGeometry.Morphisms.Etale.NormalCurveInertia`.

The extracted source is
`R5Lab.Aglib.AlgebraicGeometry.Normalization.LocalPullback` at revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`9ae9b255d05ff3194bcdf7ee2241a9335d5361cc858a6d6acdfef9c6582f26e0`.
The algebra construction is source lines 45–83; the actual-stalk construction is
source lines 93–184.

All declarations belong to
`AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.LocalComparison`.
The algebra construction retains three commutative rings in the same universe,
all three algebra structures, the exact scalar tower, localization at the stated
submonoid, and the separate invertibility-in-the-ambient-algebra hypothesis.
`IsLocalization.integralClosure` from Mathlib supplies the localization theorem.
The helper proves the corresponding `Spec` square by the algebra pushout.

For the geometric construction, `X` is integral, `C` is the original finite-etale
cover of `Spec X.functionField`, `U` is a nonempty affine open, and `y : U` is the
actual point. The ambient algebra is literally
`Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U)`.
Its stalk action factors through the actual function field. The proof derives
invertibility of every denominator outside `hU.primeIdealOf y` in that same
ambient algebra.

The source `normalization X C` is replaced by
`(C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).normalization`.
The source `structureMap X C` is its native `.fromNormalization`.
The source chart map is the native `.normalizationOpenCover.f ⟨U, hU⟩`.
`localToNormalization` composes that chart map with `Spec.map` of the actual
integral-closure inclusion. `localNormalization_isPullback` pastes the new
localization square with the existing native `isPullback_chart` square and uses
`hU.fromSpecStalk_eq_fromSpecStalk` for the base map. `localFiberIso` is the
resulting `IsPullback.isoPullback`, and the last theorem transports etaleness
along that constructed isomorphism.

No target normality, Noetherianity, regularity, source nonemptiness, or etaleness
of the normalization is assumed in this local comparison. The local closure's
etaleness remains the explicit hypothesis of the transport theorem. This leaf
neither creates a second normalization nor assumes a local comparison dictionary.
