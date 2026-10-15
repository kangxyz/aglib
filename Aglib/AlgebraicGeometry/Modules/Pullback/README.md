# Canonical module pullback comparisons

[Free](Free.lean) constructs actual pullback comparisons for the structure module, free sheaves and open restriction. The unit/free generator index sets are retained; the maps come from the native pullback adjunction.

[FlatMorphism](FlatMorphism.lean), imported as `Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism`, gives `Scheme.Modules.pullbackModuleStalkIso` with extension of scalars along the actual stalk map. `flatExactPullback` and `shortExact_pullback_of_flat_all` retain flatness of the scheme morphism for exactness on arbitrary coefficients.

[OpenRestriction](OpenRestriction.lean) owns generic restriction/sheafification and pullback-square helpers below the invertible tier. The actual owners include `Scheme.Modules.Pullback.OpenRestriction` and `PresheafOfModules.Restriction`; `PresheafOfModules.isIso_of_locallyBijective` and `Scheme.Modules.locallyBijective_of_local_isIso` use the original local sheafification maps.

Consumers are finite-presentation/quasicoherent transport, [arbitrary vector-bundle pullback](../LocallyFree/README.md), invertible tensor pullback and cohomological base change. Exactness for all module sheaves under a flat morphism and exactness for locally split vector-bundle sequences under arbitrary morphisms are separate results.

[Unit](Unit.lean), [StalkUnit](StalkUnit.lean) and [SectionStalk](SectionStalk.lean) fix the original pullback unit and its actual section/germ and stalk scalar-extension formulas. They are lower maps used by canonical projection and base-change comparisons, not additional curve/coherent interfaces.
