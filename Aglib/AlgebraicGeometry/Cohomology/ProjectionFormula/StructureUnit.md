# Original structural unit and the projection formula

Source: [StructureUnit.lean](StructureUnit.lean).

This leaf retains the installed tensor, ordinary geometric adjunction, derived
single units and derived projection-formula isomorphism. The right-unitor
section calculation and ordinary structural-unit equation have no local
freeness assumption. The derived projection square uses a finite locally free
target coefficient, exactly as the existing native projection formula requires.

## Original arbitrary-section coefficient factorization

`derivedProjectionFormulaIso_sectionUnit` proves the whole projection-formula
square for any original section `s : O_X -> Q`, an arbitrary scheme morphism,
and a finite locally free target coefficient. The ordinary adjunction unit
and original right-unit insertion appear in its conclusion. No quasicoherence,
properness, exceptional geometry, or asserted coefficient square is an input.
The proof uses original single-unit naturality, the existing projection-formula
single-unit square, and the original ordinary structural-unit law.

This factorization uses both native tensor single units forward, with no
inverse or invertibility premise on either in its statement. The existing
coefficient-unit isomorphism proof reuses the generic constructor-level
`isIso_rightDerivedSingleUnit_of_isIso_unit` in place of its two duplicated
single-complex proofs. The regular-point positive-exceptional tensor-rho is
the concrete downstream consumer.

## Current section-coefficient inference boundary

Direct consumers: [AlgebraicGeometry/Cohomology/Blowup/RegularPoint/ExceptionalPositive](../Blowup/RegularPoint/ExceptionalPositive.md), [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/Trace/IsIso](../Duality/Projective/Relative/NormalSurface/Trace/IsIso.md).
