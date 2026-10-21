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

[GenericProjection](GenericProjection.lean) extracts a full-row square
minor with nonzero determinant from spanning columns over a nontrivial
commutative ring. With finitely many columns, the determinant of the generic
linear projection is a nonzero polynomial, and coordinate-selection
specialization recovers the selected minor.
[GenericCoordinateProjection](GenericCoordinateProjection.lean) places this
determinant in the polynomial ring of the whole generic coordinate matrix,
using a specified row embedding and injective variable renaming. These
statements use the actual spanning hypothesis rather than a supplied
nonzero-minor or rank witness.
