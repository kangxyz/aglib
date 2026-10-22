# Matrices, minors and changes of generators

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

[MinorIdealValuation](MinorIdealValuation.lean) selects an actual nonzero minor
generating a nonzero minor ideal over a domain DVR, even for arbitrary row
and column types. [SelectedMinorRows](SelectedMinorRows.lean) retains that
whole ideal after selecting the rows. Given such a generating minor over a
local domain, [NormalizedProjection](NormalizedProjection.lean) constructs a
normalized generic determinant with a specialization equal to one, and
[RetainedAdjugate](RetainedAdjugate.lean) constructs the corresponding
nonzero residual condition using the adjugate of the same generic matrix.
These polynomial conditions retain the supplied selected minor.

[MinorIdealRank](MinorIdealRank.lean) obtains a nonzero row relation from
vanishing maximal minors over a field with finitely many columns.
[MinorIdealResidue](MinorIdealResidue.lean) reflects the required vanishing
along an actual local homomorphism. [ChangeOfGenerators](ChangeOfGenerators.lean)
lifts a nonzero residual relation to a unit-pivot row replacement and proves
that an invertible change preserves the original equation ideal and its
points. The Néron centre-step construction consumes these operations.
