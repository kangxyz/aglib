# Tensor pushforward for actual module presheaves

[TensorPushforward](TensorPushforward.lean), imported as `Aglib.Algebra.Category.ModuleCat.Presheaf.TensorPushforward`, gives `PresheafOfModulesOfCommRing.pushforwardTensorHom` on actual module presheaves over commutative-ring presheaves and a specified coefficient map over the underlying functor. It retains the literal pure-tensor formula and naturality.

`pushforwardTensorIso` requires the supplied coefficient natural transformation to be invertible. This is a coefficient-restriction comparison, not an invertibility assertion for arbitrary geometric direct image. Source/target category and coefficient universes remain independent where stated.

The sheafified comparison lives in [Sheaf](../Sheaf/README.md), with its continuity/sheafification hypotheses. Scheme tensor, open restriction and projection-formula maps consume these original presheaf arrows.

[SheafificationRestriction](SheafificationRestriction.lean) owns `PresheafOfModules.Restriction.restrictPresheaf`, the original sheafification unit restricted to a slice, and its locally injective/surjective and sheafification-isomorphism comparisons. Base-site and slice-site weak sheafification/local-bijectivity assumptions remain separate. `PresheafOfModules.isIso_of_locallyBijective` retains both actual sheaf hypotheses. These constructions precede scheme pullback and do not require a scheme.
