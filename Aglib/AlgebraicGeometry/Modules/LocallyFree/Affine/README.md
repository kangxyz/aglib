# Finite projective affine sections and finite-free retracts

[LocalBases](LocalBases.lean) transports the actual finite local bases to principal affine opens. [Projective](Projective.lean), imported as `Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Projective`, gives `Scheme.Modules.finitePresentation_globalSections_of_finiteLocallyFree` and `projective_globalSections_of_finiteLocallyFree`: a finite locally free sheaf on `Spec R` has a finitely presented, projective module of actual global sections over any commutative ring `R`.

[Retract](Retract.lean) constructs `exists_retract_finiteFree` for the actual affine sheaf. `isIso_app_affineBundle_of_unit_general` propagates a natural transformation's invertibility from the unit to a finite locally free affine sheaf for additive functors into the stated preadditive category. Its zero-object variant retains the same additive/unit hypothesis.

These are object/retract properties, not a newly selected category equivalence with all projective modules. They supply finite-free reductions for [tensor injective preservation](../Tensor/README.md) and arbitrary-morphism projection formula. No Noetherian or globally free assumption is inserted.
