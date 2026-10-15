# Structure-module sections and direct image

[Pushforward](Pushforward.lean), imported as `Aglib.AlgebraicGeometry.Modules.StructureSheaf.Pushforward`, defines `AlgebraicGeometry.Scheme.Modules.pushforwardStructureSheaf f` for every scheme map. It is the actual scalar-restricted `f_* O_X` using the native module direct-image functor.

[Sections](Sections.lean) lets actual global structural sections act on the unit module through their restrictions. `Scheme.Modules.unitMul` retains the literal multiplication formula and unit law, with naturality of the original sheaf arrows.

Canonical pulled-back-unit comparison and `structureModuleBaseChangeMap` live in [BaseChange](../BaseChange/README.md). Structural scalar actions on actual cohomology are defined in [Cohomology/Modules](../../Cohomology/Modules/README.md). The construction needs no smoothness, properness, curve or finite-degree premise.
