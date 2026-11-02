# Original closed-adjoint resolution naturality

Source: [ResolutionNaturality.lean](ResolutionNaturality.lean).

`derivedClosedImmersionRightAdjointModelHomologyIso_naturality` gives the
coefficient square for the installed original derived closed right adjoint,
its original model homology isomorphism, and every supplied injective-resolution
lift. It retains arbitrary integer degree and arbitrary coefficient modules.
There is no Noetherianity or quasicoherence premise for this first theorem.

`closedImmersionRightAdjointQuotientResolutionHomologyIso_naturality` gives the
corresponding original tilde-counit square for an actual quotient ideal over a
Noetherian affine ring. Both coefficients are quasicoherent, as required by
the existing counit quasi-isomorphism supplier. All integer degrees remain.

The first proof uses the native original derived-unit naturality and native
localization/homology factorization. The second uses the same actual quotient
resolution and counit, not an independently selected model. Standard scheme
module derived categories remain exactly the ones in the original constructor.
