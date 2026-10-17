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

## Module presheaf sources

[PresheafSource](PresheafSource.lean) constructs
`InternalHom.PresheafSource.sheaf X P N` for an arbitrary module presheaf
`P : PresheafOfModules X.ringCatSheaf.obj` and an arbitrary module sheaf `N`.
Its sections over `U` are the additive natural transformations from `P` to
`N` on the opens below `U` whose components are linear over the structure
sheaf, exactly as in the original `InternalHom.sheaf`: the raw Hom presheaf
uses only the underlying abelian presheaf of the source, and the sheaf
condition (`N.isSheaf.hom`) and the locality of linearity
(`InternalHom.PresheafSource.linearity_isLocal`) come from the target. For the
underlying presheaf of a module sheaf `M`, the construction is definitionally
`InternalHom.sheaf X M N`. No sheaf, quasicoherence or finiteness condition is
imposed on `P`.

[PresheafTensor](PresheafTensor.lean) supplies the tensor–Hom bijection
`InternalHom.PresheafSource.tensorHomEquiv X P Q N :
(P ⊗ Q ⟶ N.val) ≃ (Q ⟶ (InternalHom.PresheafSource.sheaf X P N).val)`
for module presheaves `P`, `Q` with Mathlib's pointwise tensor product on
`PresheafOfModulesOfCommRing X.sheaf.obj`. Currying sends a local section `q`
to the Hom-sheaf section `p ↦ h (p ⊗ q)`; uncurrying evaluates the section
attached to `q` at `p` (`InternalHom.PresheafSource.uncurry_app_tmul`).
`InternalHom.PresheafSource.tensorHomEquiv_whiskerLeft_comp` proves
naturality in `Q`: whiskering by `P` corresponds to precomposition. No
sheafification occurs. The present consumer is the stability of local
isomorphisms of module presheaves under tensor products in
[Tensor/Monoidal/LocalIso](../Tensor/Monoidal/LocalIso.lean).

`PresheafSource` duplicates the construction of the original
`InternalHom.sheaf` in [InternalHom](../InternalHom.lean) (lines 36-210),
with the source presheaf `M.val` replaced by an arbitrary `P`; the `rfl`
example in the [focused consumer](../../../../AglibTest/AlgebraicGeometry/Modules/InternalHom/PresheafTensor.lean)
checks that the two agree. A later step will delegate the original to the
presheaf-source version, `InternalHom.sheaf X M N :=
PresheafSource.sheaf X M.val N` (and its helpers likewise); it is not done
here because it edits existing files and their consumers.

The two tensor–Hom bijections curry opposite factors. The sheaf-level
`Pullback.Tensor.tensorHomEquiv`
([Pullback/Tensor/Isomorphism](../Pullback/Tensor/Isomorphism.lean)) is
`(tensorSheaf X M N ⟶ P) ≃ (M ⟶ InternalHom.sheaf X N P)`: it keeps the
first factor and takes the Hom out of the second. The presheaf-level
`InternalHom.PresheafSource.tensorHomEquiv X P Q N` keeps the second factor
`Q` and takes the Hom out of the first factor `P`, following Mathlib's
closed-monoidal convention `tensorLeft P ⊣ ihom P`.
