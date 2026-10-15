# Actual scheme–algebra coefficient base change

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.BaseChange.Coefficients.Basic`, uses `AlgebraicGeometry.Scheme.BaseChange.Coefficients.Index R`: actual schemes over `Spec R` and algebras in `Under R`, with the stated opposite variance. `space`, `projection` and `coefficientProjection` are the actual fibre product and its two projections.

`functor`, `row`, `rowTransformation` and `schemeMap` package the original scalar/scheme maps. `schemeMap_isPullback` proves the actual cartesian square; `identityProjectionIso` gives the comparison at the identity algebra. Compactness and quasi-separatedness transport retain the stated property of the original scheme.

[PolynomialLaurent](PolynomialLaurent.lean), [PolynomialLaurentNaturality](PolynomialLaurentNaturality.lean) and [PolynomialLaurentSchemeNaturality](PolynomialLaurentSchemeNaturality.lean) specialize these diagrams to the actual polynomial/Laurent coefficient maps and retain naturality in both variables. No field, Noetherian, smoothness or fixed-dimension premise is imposed merely to construct the family.

Consumers are relative polynomial/Laurent geometry and actual module/base-change comparisons. The underlying [algebra diagrams](../../../../Algebra/Polynomial/Laurent/README.md) and ordinary scheme pullbacks remain the lower objects.

[Naturality](Naturality.lean), imported as `Aglib.AlgebraicGeometry.Modules.BaseChange.Coefficients.Naturality`, proves `Scheme.BaseChange.Coefficients.coefficientMap_naturality`. For an arbitrary scheme `P` over `Spec R`, a natural transformation between endofunctors of `Under R` and an actual algebra-index arrow give the commuting square of the original coefficient scheme maps. This statement adds no perfect-complex, flatness or boundedness hypothesis.
