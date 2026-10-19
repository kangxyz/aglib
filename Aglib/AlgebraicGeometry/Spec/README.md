# Spectrum constructions and relative polynomial/Laurent schemes

[PolynomialLaurent](PolynomialLaurent/README.md) constructs polynomial and Laurent
spectra over arbitrary commutative coefficient rings, their actual projections,
coordinate open immersions, Laurent coordinate unit and polynomial zero section.
The relative product functors act on arbitrary quasi-compact base schemes and
unrestricted morphisms in that full category. Those bases need not be affine.

The lower [polynomial/Laurent algebra diagrams](../../Algebra/Polynomial/Laurent/README.md)
fix the coefficient maps. [Scheme-valued coefficient base change](../BaseChange/Coefficients/README.md)
and [integer-base products](../Products/README.md) provide the geometric
comparison routes. Individual statements retain their quasi-compactness,
coefficient and cartesian-square data. These constructions introduce no
projective-line, curve, degree or K-theory application object.

[Localization](Localization.lean), imported as `Aglib.AlgebraicGeometry.Spec.Localization`, gives the actual spectral square of canonical principal localization maps and the resulting closed-immersion and quotient-to-base morphism consequences. Local quasi-finiteness, flatness and local finite presentation each retain their own stated premise. These constructions have no smoothness, Cartier or ideal-module hypothesis; their ring equations are supplied by the lower [CommRingCat localization API](../../Algebra/Category/Ring/Localization.lean).

[ResidueField](ResidueField.lean), imported as `Aglib.AlgebraicGeometry.Spec.ResidueField`, proves `Spec.map_algebraMap_residueField_closedPoint`: the residue map of a prime `P` induces a morphism `Spec κ(P) ⟶ Spec A` sending the closed point to `P`.
