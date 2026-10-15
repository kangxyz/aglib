# The actual projection-formula map

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.ProjectionFormula.Basic`, constructs `Scheme.Modules.projectionFormulaMap f E M` for actual module sheaves: `E ⊗ f_*M → f_*(f*E ⊗ M)`. Its forward map is built from native tensor/direct-image and adjunction maps. The section formula and coefficient naturality identify that map.

[FiniteLocallyFree](FiniteLocallyFree.lean) supplies `isIso_projectionFormulaMap` and `projectionFormulaIso` for an arbitrary scheme morphism with finite locally free target coefficient `E`, and arbitrary source coefficient `M`. Flatness or Noetherianity of the scheme map is not assumed. Local finite bases reduce the map to its actual affine finite-free comparison.

[ClosedImmersion](ClosedImmersion.lean) instead gives `isIso_projectionFormulaMap_of_closedImmersion` with arbitrary `E` and `M`. It supplies natural comparison isomorphisms in both coefficient variables, retaining the original projection map; no finite-local-free hypothesis is needed in this closed case.

[Affine](Affine.lean), [OpenBaseChange](OpenBaseChange.lean) and [Stalk](Stalk.lean) fix scalar restriction, cartesian-open and actual stalk comparisons. Their affine/square/open and local isomorphism hypotheses remain attached to each source statement. [D+ projection formula](../../Cohomology/ProjectionFormula/README.md) is a later consumer and retains finite local freeness for its derived tensor interface.
