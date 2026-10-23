# Finite-type field points

For the actual map `c : Spec K ⟶ S`, with `K` a field and `c` locally of finite
type, `Scheme.Hom.isLocallyClosed_range_of_field` proves that its singleton
image is locally closed when `S` is locally Noetherian.
`Scheme.Hom.exists_affine_closedPoint_lift_of_field` produces an actual affine
open `V` and a factorization `cV : Spec K ⟶ V`, with `cV ≫ V.ι = c`, whose point
is closed in `V`. The field remains the original full `K`.
`Scheme.Hom.exists_affine_finite_lift_of_field` strengthens this construction
to an actual finite morphism `cV : Spec K ⟶ V` with the same factorization.

The proof uses pinned Mathlib's locally Noetherian finite-type-to-finite-
presentation instance and `Scheme.Hom.isLocallyConstructible_image` (Chevalley,
Stacks 054K). A constructible singleton is locally closed: a member of a finite
union of differences of open sets lies in one locally closed piece, and that
piece equals the singleton. The same argument on a neighborhood treats locally
constructible singletons. An affine neighborhood inside the resulting open
then makes the point closed.

Without a Noetherian hypothesis on `S`,
`Scheme.Hom.finite_descResidueField_of_field` proves finiteness of the canonical
map `S.residueField (c (IsLocalRing.closedPoint K)) ⟶ K`, namely
`S.descResidueField (Scheme.stalkClosedPointTo c)`. It factors the original
scheme map through the canonical residue-field point, applies
`locallyOfFiniteType_of_comp`, and uses Zariski's lemma in
`RingHom.finite_iff_finiteType_of_isJacobsonRing`. Neither a replacement field
nor an independently chosen residue-field embedding is introduced.

`Scheme.Hom.isFinite_of_field_of_isClosed_image` combines that finiteness
with the canonical closed residue-field immersion when the image point is
closed. This result has no Noetherian hypothesis; applying it after the affine
shrink gives `exists_affine_finite_lift_of_field`.

These are prerequisites for shrinking the base in the C6 surface-contraction
argument corresponding to Stacks 0C2N. Properness over the original whole base
is not asserted by this module.

Source basis: Aglib `c6f64b5b133624fae3ad8650f456194180be7ba2`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1. The proofs are new
packaging of the cited pinned APIs. Compilation is performed by the principal's
prepared incremental remote batch.
