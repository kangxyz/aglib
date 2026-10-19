# Canonical module pullback comparisons

[Free](Free.lean) constructs actual pullback comparisons for the structure module, free sheaves and open restriction. The unit/free generator index sets are retained; the maps come from the native pullback adjunction.

[FreeComp](FreeComp.lean) proves that `pullbackFreeIso` respects Mathlib's composition, identity and equality comparisons of pullbacks (`pullbackFreeIso_comp`, `pullbackFreeIso_id`, `pullbackFreeIso_congr`); the first two are checked on the summand inclusions through `pullbackUnitIso_comp` and `_id`. Its consumer is the quotient functor of [Grassmannian/Quotient](../../Grassmannian/README.md).

[FlatMorphism](FlatMorphism.lean), imported as `Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism`, gives `Scheme.Modules.pullbackModuleStalkIso` with extension of scalars along the actual stalk map. `flatExactPullback` and `shortExact_pullback_of_flat_all` retain flatness of the scheme morphism for exactness on arbitrary coefficients.

[OpenRestriction](OpenRestriction.lean) owns the actual scheme restriction/pullback-square helpers below the invertible tier. The arbitrary-site `PresheafOfModules.Restriction` constructions and `PresheafOfModules.isIso_of_locallyBijective` are imported from [module-presheaf sheafification restriction](../../../Algebra/Category/ModuleCat/Presheaf/SheafificationRestriction.lean). The scheme criterion `Scheme.Modules.locallyBijective_of_local_isIso` consumes the same original local maps.

Consumers are finite-presentation/quasicoherent transport, [arbitrary vector-bundle pullback](../LocallyFree/README.md), invertible tensor pullback and cohomological base change. Exactness for all module sheaves under a flat morphism and exactness for locally split vector-bundle sequences under arbitrary morphisms are separate results.

[Unit](Unit.lean), [StalkUnit](StalkUnit.lean) and [SectionStalk](SectionStalk.lean) fix the original pullback unit and its actual section/germ and stalk scalar-extension formulas. They are lower maps used by canonical projection and base-change comparisons, not additional curve/coherent interfaces.
