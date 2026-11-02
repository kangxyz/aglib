# Original stalk and residue-point section maps

`PointSections.lean`, in `AlgebraicGeometry.Scheme`, owns the four generic
point-section laws formerly proved in `Cohomology/Proper/FibreIdempotents`.
The old qualified names remain thin facades with their original headers.
The original fibre-section construction and its later proofs are unchanged.

For an arbitrary scheme, point and open neighbourhood, `stalkRestriction_le`
and `residueRestriction_le` prove that the preimage of that neighbourhood is
the whole original stalk or residue-field spectrum. `stalkPoint_appLE` and
`residuePoint_appLE` identify the actual section maps with the original germ,
residue quotient where applicable, and canonical `Gamma(Spec)` comparison.
They do not choose another field, stalk, scheme or algebra action.

`ker_evaluation_eq_primeIdealOf` identifies the kernel of the native
`Scheme.evaluation` on an actual affine neighbourhood with that affine
open's original `primeIdealOf`. It uses the original germ, the native
closed-point prime of the stalk and `IsLocalRing.ker_residue`, not support
or radical equality.

These laws require no properness, closedness of the point, Noetherianity,
regularity, dimension, domain, or finite-type hypothesis. Every scheme,
section ring, original stalk and residue field remains in its native scheme
universe. There is no additional supplied algebra or field model.

The complete native owner passed as exact source `eadd757f` in own187:
2.7 s leaf, 5.7590 s total, 2514 jobs, exit 0 with no aggregate guard and
the owned process group gone. This includes the exact evaluation-kernel law,
not only the moved point-section block. The actual ideal-sheaf consumer
`ResiduePoint` and original `FibreIdempotents` owner separately passed in
own189 and own190. Their original app/appLE restriction remains explicit.
The regular-pair-on-an-affine-neighbourhood and global one-pole constructions
remain separate work; these owner checks do not establish them.
