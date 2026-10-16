# Native closed right adjoint in bounded-below cohomology

[RightAdjoint](RightAdjoint.lean) defines
`derivedClosedImmersionRightAdjointPlus` as the actual right-derived functor
of the single selected ordinary `closedImmersionRightAdjoint`, on the
installed standard categories of all scheme module sheaves.

`derivedClosedImmersionRightAdjointOpenIso` derives the original ordinary
[open comparison](../../Modules/ClosedImmersion/RightAdjoint/Restriction.lean)
through the existing native composition comparisons. Exactness of source
restriction and preservation of injectives by target restriction discharge
the two composition conditions. Its `_unit` theorem retains the original
ordinary comparison and both installed composite-derived units. The
independent arbitrary-universe consumer checks those exact arrows and uses
only the standard three axioms.

This locality interface is an input to the affine coinduction/Koszul
calculation of purity. It does not yet identify the derived object with a
shifted canonical line or assume QC preservation by the ordinary adjoint.
