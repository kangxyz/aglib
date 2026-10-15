# Products over the integer base

[IntegerBase](IntegerBase.lean), imported as `Aglib.AlgebraicGeometry.Products.IntegerBase`, uses `Scheme.Products.integerBase`, the actual spectrum of the integer ring, and the natural map `toIntegerBase` from every scheme. The filename refers to the integer base, not an assumption that the scheme is integral.

`baseProductFunctor` and `baseProductTransformation` use the original fibre products over that base. A compatible morphism `f` with the actual structural-map equation gives `baseProductTransformation_isPullback`. No field or integrality hypothesis is required.

`qcBaseProductFunctor` and its transformation restrict to actual [quasi-compact schemes](../Properties/QuasiCompactCategory.lean), retaining the stated quasi-compactness of the base maps. Relative polynomial/Laurent families are consumers of these canonical products and projections.
