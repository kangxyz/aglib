# Effective Cartier consequences for actual closed ideals

These pointwise interfaces concern a closed immersion whose actual kernel ideal module is locally rank one. They use the existing `Scheme.Hom.idealModule` and native invertible-module condition.

[FinitePresentation](FinitePresentation.lean), imported as `Aglib.AlgebraicGeometry.EffectiveCartierDivisor.FinitePresentation`, proves that such a closed immersion is locally of finite presentation. No base, smoothness, flatness or Noetherian premise is needed. A separate composition result retains local finite presentation of the displayed ambient structure morphism.

The [smooth relative-dimension-one family](Smooth/README.md) proves invertibility of finite flat closed ideals and the converse local quasi-finiteness statement over arbitrary bases. [Fibrewise regular line-bundle maps](../Modules/Invertible/ZeroLocus/README.md) produce actual monic maps and flat zero-scheme composites through the proved arbitrary-base ring criterion.

[Relative](Relative/README.md) defines relative effective Cartier divisors. It proves base change; the fiberwise criterion over arbitrary bases for `p` flat and locally of finite presentation with `D ⟶ T` flat and locally of finite presentation (Kleiman, Lemma 3.4; Stacks Project, Tag 062Y); openness of the locus of Cartier fibers when the base is locally Noetherian, `p` is flat, locally of finite type and universally closed, and `D` is flat (proof of Kleiman, Thm 3.7); and the base-change characterization of that locus.
