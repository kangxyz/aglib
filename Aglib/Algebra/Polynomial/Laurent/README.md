# Natural polynomial–Laurent algebra maps

[BaseChange](BaseChange.lean), imported as `Aglib.Algebra.Polynomial.Laurent.BaseChange`, uses `CommRingCat.PolynomialLaurent` for actual coefficient inclusions, polynomial and Laurent scalar maps, inversion and the specified evaluation maps. Ring-map naturality retains the literal maps on coefficients and the Laurent variable.

[Square](Square.lean) gives identity/composition and the original commuting polynomial-to-Laurent squares. [UnderSquare](UnderSquare.lean) packages these maps in the actual under-category, with `polynomialUnderFunctor`, `laurentUnderFunctor` and their forgetful comparison.

Coefficient rings are arbitrary commutative rings. The consumers are [actual polynomial/Laurent spectra](../../../AlgebraicGeometry/AffineSpace/PolynomialLaurent/README.md) and [scheme/algebra coefficient base change](../../../AlgebraicGeometry/Modules/BaseChange/Coefficients/README.md). No finite type, field or characteristic premise is added to the literal scalar maps unless a particular property result requires it.
