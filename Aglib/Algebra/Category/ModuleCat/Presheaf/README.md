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

[ExteriorPower](ExteriorPower.lean) constructs the actual pointwise exterior
power of a module presheaf over any presheaf of commutative rings. Its
values are exactly `ModuleCat.exteriorPower`; its restrictions use the
original `restrictₛₗ` and the native semilinear exterior map. The literal
wedge restriction and coefficient formulas, identity and composition are
proved before assembling `exteriorPowerFunctor`. Ring, module, category
object and category morphism universes are independent; the exterior
carrier has the required maximum of ring and module sizes. No finiteness,
field or localization hypothesis is imposed. The immediate consumer is
the exterior-power functor on actual module sheaves through their original
sheafification, followed by determinant and canonical-bundle comparisons.

[ExteriorPower.Universal](ExteriorPower/Universal.lean) proves the actual
universal property. A compatible alternating family consists of native
sectionwise `ModuleCat.AlternatingMap`s with the original module restriction
equations. `exteriorPowerHomEquiv` identifies these families with morphisms
from the same exterior presheaf. Its forward map evaluates on the original
wedge, and its inverse is the original native exterior descent at every
object. Coefficient postcomposition and the canonical wedge family retain
these formulas. No supplied universal-property premise is used.
