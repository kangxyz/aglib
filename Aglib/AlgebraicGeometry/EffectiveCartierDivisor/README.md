# Effective Cartier consequences for actual closed ideals

These pointwise interfaces concern a closed immersion whose actual kernel ideal module is locally rank one. They use the existing `Scheme.Hom.idealModule` and native invertible-module condition.

[FinitePresentation](FinitePresentation.lean), imported as `Aglib.AlgebraicGeometry.EffectiveCartierDivisor.FinitePresentation`, proves that such a closed immersion is locally of finite presentation. No base, smoothness, flatness or Noetherian premise is needed. A separate composition result retains local finite presentation of the displayed ambient structure morphism.

The [smooth relative-dimension-one family](Smooth/README.md) proves invertibility of finite flat closed ideals and the converse local quasi-finiteness statement over arbitrary bases. [Fibrewise regular line-bundle maps](../Modules/Invertible/ZeroLocus/README.md) produce actual monic maps and flat zero-scheme composites through the proved arbitrary-base ring criterion.
