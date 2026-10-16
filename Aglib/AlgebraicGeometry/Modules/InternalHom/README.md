# Original module morphisms and the Hom sheaf

The original [InternalHom](../InternalHom.lean) constructs the structure-linear
Hom sheaf for arbitrary native scheme module sheaves. Its original
`InternalHom.sectionHomEquiv` identifies sections over an open with actual
module morphisms over that open.

[Restriction](Restriction.lean) supplies
`InternalHom.restrictionHomEquiv j M N` for an actual open immersion `j : U ⟶ X`.
It identifies actual arrows `M.restrict j ⟶ N.restrict j` with sections of the
original Hom sheaf on `j.opensRange`. The construction retains the original
image/preimage section isomorphisms, original scalar actions, and original
component maps. The forward and inverse component equations evaluate on the
same original image open `j ''ᵁ V`.

`InternalHom.restrictionHomEquiv_restrict` proves that restricting the original
Hom-sheaf section is exactly further actual open restriction.
`InternalHom.restrictionHomMap` retains the native `restrictFunctorComp`
comparison maps in that equation. No quasicoherence, finiteness, affineness,
field, or nontriviality assumption is imposed on either module or scheme.

[Gluing](Gluing.lean) constructs `InternalHom.globalHomEquiv`, identifying
original global module morphisms with global sections of the same Hom sheaf.
`InternalHom.RestrictionHomCompatible` is the literal native equality on each
actual pullback overlap, through `Scheme.Modules.overlapRestrictIso`.
`InternalHom.restrictionHomSections_overlap` proves that this equality gives
matching original Hom-sheaf sections on the range intersection.

`InternalHom.existsUnique_restrictionHom` glues compatible local arrows on a
jointly covering native open family to a unique actual global module morphism.
`InternalHom.glueRestrictionHom` chooses that unique morphism;
`InternalHom.glueRestrictionHom_restrict` and
`InternalHom.glueRestrictionHom_unique` retain the exact native restriction
and uniqueness equations. The index universe is independent of the scheme
universe. Empty covers on empty schemes are included, with no inhabitedness,
quasicoherence, finiteness, or field premise.
