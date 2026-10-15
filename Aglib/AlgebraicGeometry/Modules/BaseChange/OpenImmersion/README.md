# Open base change in an actual cartesian square

[Cartesian](Cartesian.lean), imported as `Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian`, specializes the native generic `Scheme.Modules.openBaseChange` primitive to a supplied square `a : W ⟶ U`, `b : W ⟶ V`, `f : U ⟶ X`, `j : V ⟶ X` with `IsPullback a b f j` and open immersions `a,j`. [CartesianSections](CartesianSections.lean) proves the original section/unit component formulas.

The open-immersion and `IsPullback` hypotheses identify the maps and source/target restrictions. No quasicoherence or coherent-category premise is needed for this module-sheaf comparison. `Scheme.Modules.opensRange_of_isPullback` is the exact alias of the canonical geometric `Scheme.Hom.opensRange_of_isPullback` in the [open-immersion family](../../../Morphisms/OpenImmersion/README.md); it introduces no second implementation.

Projection-formula localization, Godement section spans and base-change unit diagrams consume these actual square maps. General flat derived base-change maps have their own additional flatness/unit conditions.

[Pullback](Pullback.lean) identifies that restriction isomorphism with the
original geometric `cartesianBaseChangeMap`, using
`restrictFunctorIsoPullback` and the original adjunction units.
`cartesianOpenBaseChange_pullback` gives the actual forward-map equation;
`isIso_cartesianBaseChangeMap_of_isOpenImmersion` proves invertibility of the
original mate for every module sheaf. The displayed square and its two open
immersions remain the only hypotheses, without quasicoherence or flatness.

[Units](Units.lean) proves
`cartesianPullbackBaseChangeMate_inv_unit_comp`. The inverse of the original
pullback/restriction mate identifies the two composite coefficient arrows
through the square, using the original restriction and pullback units,
direct-image composition and equality comparison. Geometric cohomology
restriction consumes this exact original-arrow equation.
