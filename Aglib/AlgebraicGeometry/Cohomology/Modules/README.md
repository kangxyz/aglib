# Coefficients, structural scalars and H0

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.Modules.Basic`, defines `AlgebraicGeometry.Scheme.Cohomology.moduleAddSheaf`, `moduleScalar` and `moduleCohomology`. The last object is the actual additive `Sheaf.H` of a module sheaf on a field scheme, with scalar action induced by structural constants. `moduleCohomologyMap` and `moduleCohomologyIso` are the corresponding actual coefficient map/isomorphism.

`moduleH0Equiv` is a structural-field linear equivalence with actual global sections. `structureModuleCohomologyEquiv` compares the unit module's cohomology with the unchanged structure-sheaf cohomology and its scalar action. No finiteness premise is needed for these constructions or H0 comparisons.

[StructureSheaf](StructureSheaf.lean) owns `Scheme.structureAddSheaf`, `structureScalar`, `structureCohomology` and `structureH0Equiv`. [Constants](Constants.lean) separately owns `Scheme.constants` and `constantSection`: actual structural ring maps into section rings, with restriction compatibility. [StalkScalars](StalkScalars.lean) identifies the action on native module stalks with the action induced by `moduleScalar`, through constant-germ equality; it is not a finite-support-only result.

Fields/schemes use universe `u`, while cohomology is in `Type (u+1)`. Focused imports follow these four leaves. Functoriality, long exactness, finite support, finiteness and base change consume these same objects and actions.
