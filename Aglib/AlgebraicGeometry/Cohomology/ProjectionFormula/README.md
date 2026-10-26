# The actual D+ projection formula

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.ProjectionFormula.Basic`, constructs `Scheme.Modules.derivedProjectionFormulaIso`, using the ordinary `projectionFormulaNatIso` from [finite locally free module coefficients](../../Modules/ProjectionFormula/FiniteLocallyFree.lean). For an arbitrary scheme morphism and finite locally free target coefficient `E`, the D+ comparison uses the actual tensor, pullback and derived direct-image functors.

`derivedProjectionFormulaIso_unit` identifies the forward comparison with the original installed derived unit and canonical module projection-formula map. [TensorPushforward](TensorPushforward.lean) supplies the actual right-derived composition calculation and unit-isomorphism results for finite locally free tensor, retaining the stated injective/acyclic computation premises.

The comparison uses the shared `rightDerivedFunctorPlusThreeFactorIso` and
its whole composite-unit law. `derivedProjectionFormulaIso_eq_original`
identifies its value with the original three factors, including the selected
`tensorPushforwardDerivedCompIso` obtained from native composite derivability.
The input complex remains an arbitrary bounded-below module complex.

Lower [module projection formula](../../Modules/ProjectionFormula/README.md) and [finite-locally-free tensor exactness](../../Modules/LocallyFree/Tensor/README.md) feed this comparison. Godement projection-formula maps additionally retain termwise flasqueness of the bounded-below complex. The arbitrary-coefficient closed-immersion module result is not silently promoted to this derived interface.
