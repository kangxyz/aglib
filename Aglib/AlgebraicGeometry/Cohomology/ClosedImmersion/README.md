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

The comparison is an instance of the shared
`rightDerivedFunctorPlusThreeFactorIso`; its `_eq_original` theorem retains
the original homology-preservation and injective-preservation factors, and
the generic composite-unit law supplies the existing component equation.

This locality interface is an input to the affine coinduction/Koszul
calculation of purity. It does not yet identify the derived object with a
shifted canonical line or assume QC preservation by the ordinary adjoint.

## Regular equations and positive Cartier purity

[RightAdjoint/Principal](RightAdjoint/Principal.md) computes the original
closed right adjoint for a regular equation over a Noetherian ring, with
quasicoherent coefficients on which that equation acts injectively. It
retains the actual quotient action, Koszul class and positive extension mate.
[Cartier](RightAdjoint/Cartier.md) constructs the original dual-ideal section
and tensor adapters; [Purity](RightAdjoint/Cartier/Purity.md) constructs the
actual coefficient row and its exactness.
[Global purity](RightAdjoint/Cartier/Purity/Global.md) derives degree-one
concentration and the positive counit-normalized isomorphism for a closed
immersion with locally rank-one kernel ideal on a locally Noetherian scheme.
The coefficient is quasicoherent and its canonical Cartier tensor section
is monic; it need not be locally free. The principal charts and concentration
are constructed, rather than supplied. These interfaces serve the later
canonical restriction comparison, which is not asserted here.
