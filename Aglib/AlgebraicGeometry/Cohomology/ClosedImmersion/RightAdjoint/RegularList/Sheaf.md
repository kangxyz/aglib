# Sheaf realization of the closed right adjoint

Source: [Sheaf.lean](Sheaf.lean).

The installed bounded-below closed right adjoint for an ordered finite weakly
regular list retains the original quotient structure sheaf, Koszul top class,
resolution unit and independent Ext and derived-category universe bounds.
Empty lists, unit quotients and zero rings remain included.

The original provider and its private resolution helpers keep their baseline
implementation. The existing public
`canonicalAffineResolutionSectionsIso_naturality` and
`canonicalAffineResolutionExt_naturality` in the
[canonical coefficient provider](../../../Duality/Projective/Canonical/LocalModel/Coefficients.lean)
supply resolution naturality when needed. An unused alias-only exposure of the
same helpers is omitted.
