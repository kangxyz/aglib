# Polynomial–Laurent spectra, relative maps and zero section

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.AffineSpace.PolynomialLaurent.Basic`, constructs the actual polynomial/Laurent spectra, structural projections, specified open-range maps and Laurent coordinate unit. [Units](Units.lean) identifies the actual global unit with its coefficient and variable formulas.

[Relative](Relative.lean) packages the ordinary relative product construction over the integer base. [BaseChange](BaseChange.lean) proves the actual scalar/spectrum comparison and naturality of the specified plus/minus maps. The lower [algebra under-category squares](../../../Algebra/Polynomial/Laurent/README.md) and [coefficient pullbacks](../../Modules/BaseChange/Coefficients/README.md) fix these maps.

[ZeroSection](ZeroSection.lean) gives `Scheme.PolynomialLaurent.polynomialZeroSection`: the spectrum map of polynomial evaluation at zero. `polynomialZeroSection_projection` proves its composite with the actual polynomial projection is the identity. The coefficient ring is an arbitrary commutative ring; no field or Noetherian premise is added to this selected construction.

Consumers are actual scheme/coefficient base change and projection/section normalization. The guide does not import the original Bass/projective-line/perfect-complex application containing the zero-section source range.
