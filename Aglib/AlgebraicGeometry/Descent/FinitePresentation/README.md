# Finite-presentation descent

These modules retain the original objects, structural maps and native
pullback comparisons over an actual filtered colimit of rings.

| Module | Actual construction |
| --- | --- |
| [Diagrams](Diagrams.md) | Canonical scheme base-change systems, their limiting cones, and common later stages for finite families of maps and equations. |
| [Gluing](Gluing.md) | Quasi-compact open models, finite open gluing and eventual isomorphisms of the specified stage maps, with quasi-separatedness required only on the target for eventual isomorphisms. |
| [Schemes](Schemes.md) | Every finitely presented qcqs scheme has a stage model; a finite category of such schemes has an actual stage functor and pullback natural isomorphism. |
| [Properties](Properties.md) | Actual schematic-image, standard-smooth and relative-dimension suppliers for finite-base curve models. |

Scheme finite presentation uses the native three conditions
`LocallyOfFinitePresentation`, `QuasiCompact` and `QuasiSeparated`.
The object and diagram theorems impose no separatedness, Noetherianity,
flatness or injectivity condition on the stage maps. Finite diagram descent
requires finitely many objects and finite hom sets, and retains every
identity and composition equation.

The comparison-preserving `Model.Map` interface represents a specified
original arrow. The binary open-gluing proof uses it to descend the identity
of the original overlap. The separate eventual-isomorphism existence theorem
suffices when only properties are transported between two given models.

[SpreadingOut](../../Morphisms/SpreadingOut.md) constructs finite integer-base
models of actual smooth proper field curves and restores their properties
on later literal base changes of a supplied stage model. Its generic-open
geometric-integrality supplier retains the smooth relative-curve scope.
