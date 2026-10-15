# Actual module presheaves

[TensorPushforward](TensorPushforward.lean), imported as `Aglib.Algebra.Category.ModuleCat.Presheaf.TensorPushforward`, gives `PresheafOfModulesOfCommRing.pushforwardTensorHom` on actual module presheaves over commutative-ring presheaves and a specified coefficient map over the underlying functor. It retains the literal pure-tensor formula and naturality.

`pushforwardTensorIso` requires the supplied coefficient natural transformation to be invertible. This is a coefficient-restriction comparison, not an invertibility assertion for arbitrary geometric direct image. Source/target category and coefficient universes remain independent where stated.

The sheafified comparison lives in [Sheaf](../Sheaf/README.md), with its continuity/sheafification hypotheses. Scheme tensor, open restriction and projection-formula maps consume these original presheaf arrows.

[ForgetToModuleCat](ForgetToModuleCat.lean) proves exactness of the native
`PresheafOfModules.forgetToPresheafModuleCat X hX` for an initial object
of an arbitrary ring-presheaf category. Pointwise scalar forgetting gives
literally the original additive `toPresheaf` functor. The native functor
is additive and preserves finite limits, finite colimits and homology.
Ring, module, category and hom universes are independent; no commutativity,
localization, sheaf or geometric hypothesis is imposed. Resolution-section
and higher-direct-image comparisons consume this exact original functor.
