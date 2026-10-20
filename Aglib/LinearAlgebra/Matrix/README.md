# Matrices of scalar restriction

[ScalarRestriction](ScalarRestriction.lean), imported as
`Aglib.LinearAlgebra.Matrix.ScalarRestriction`, constructs
`Matrix.GeneralLinearGroup.restrictedScalarMatrix` from the actual left
multiplication matrix in a supplied basis. Its determinant is the algebra norm.
The basis index is any finite type with decidable equality; no separability
hypothesis is added. Entrywise determinant naturality uses Mathlib's existing
`Matrix.GeneralLinearGroup.map_det`.

The categorical scalar-restriction squares in
[FGModuleCat.ScalarMatrices](../../Algebra/Category/FGModuleCat/ScalarMatrices.lean)
use this same matrix and the native finite restriction-of-scalars functor.
