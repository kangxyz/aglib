# Open base change in an actual cartesian square

[Cartesian](Cartesian.lean), imported as `Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian`, specializes the native generic `Scheme.Modules.openBaseChange` primitive to a supplied square `a : W ⟶ U`, `b : W ⟶ V`, `f : U ⟶ X`, `j : V ⟶ X` with `IsPullback a b f j` and open immersions `a,j`. [CartesianSections](CartesianSections.lean) proves the original section/unit component formulas.

The open-immersion and `IsPullback` hypotheses identify the maps and source/target restrictions. No quasicoherence or coherent-category premise is needed for this module-sheaf comparison. `Scheme.Modules.opensRange_of_isPullback` is the exact alias of the canonical geometric `Scheme.Hom.opensRange_of_isPullback` in the [open-immersion family](../../../Morphisms/OpenImmersion/README.md); it introduces no second implementation.

Projection-formula localization, Godement section spans and base-change unit diagrams consume these actual square maps. General flat derived base-change maps have their own additional flatness/unit conditions.
