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

[Refinement](Refinement.lean) retains the original native comparison between a
refinement square of module arrows and restriction of its Hom-sheaf section.
It also recovers native overlap compatibility from matching Hom sections.
These general laws are shared by canonical-chart descent and nonflat
higher-direct-image base change; they require no quasicoherence hypothesis.

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

For the underlying presheaf of a module sheaf, `PresheafSource.sheaf X M.val N`
agrees definitionally with `InternalHom.sheaf X M N`; both retain the original
Hom presheaf and scalar-linearity condition.

The two tensor–Hom bijections curry opposite factors. The sheaf-level
`Pullback.Tensor.tensorHomEquiv`
([Pullback/Tensor/Isomorphism](../Pullback/Tensor/Isomorphism.lean)) is
`(tensorSheaf X M N ⟶ P) ≃ (M ⟶ InternalHom.sheaf X N P)`: it keeps the
first factor and takes the Hom out of the second. The presheaf-level
`InternalHom.PresheafSource.tensorHomEquiv X P Q N` keeps the second factor
`Q` and takes the Hom out of the first factor `P`, following Mathlib's
closed-monoidal convention `tensorLeft P ⊣ ihom P`.

[HomFunctor](HomFunctor.lean) and [HomSection](HomSection.lean) expose the
actual internal-Hom functor and section interfaces used by line-bundle and
relative-evaluation constructions.

## Affine linear sections and coherence

[AffineSections](AffineSections.lean) gives the original linear section
`sectionEvaluation` and its restriction formula. [AffineEvaluation](AffineEvaluation.lean)
proves `affineSectionsEquiv` on every actual affine open, requiring only
quasicoherence of the restricted source; the target is arbitrary. Its
`affineSectionsEquiv_restrict` covers arbitrary inclusions of affine opens,
not only principal opens. [AffineRestriction](AffineRestriction.lean) gives
the same linear comparison on an explicitly specified affine open immersion.
[AffineIterated](AffineIterated.lean) preserves the native restriction-composition
isomorphisms and proves the original principal-restriction evaluation square.

[Coherent](Coherent.lean) proves
`InternalHom.affineLocallyFiniteType_internalHom`: on a locally Noetherian
scheme, the actual internal Hom of two affine-locally finite-type
quasicoherent modules has the same property. Its lower
`quasicoherent_affineRestriction` needs quasicoherent source and target and
finite presentation of source sections on the specified chart, but no
Noetherian hypothesis. The proof identifies original section restriction
with Hom localization; it does not replace the native Hom sheaf or assume
quasicoherence from stalk finiteness. No nonflat base-change assertion for
internal Hom is made.

## Completed affine comparison

For affine-locally finite-type quasicoherent source and target on a locally
Noetherian scheme, [FormalComparison](FormalComparison.lean) identifies the structural-ideal completion of original
internal-Hom sections on an affine open with compatible linear maps on the
original chart-module quotients. It uses flat completed-Hom base change, not
Hom base change at a nonflat finite stage. Affine coordinate rings need not be
complete. The comparison sends original sections to their literal evaluation
and reduction maps.

[CompletedEvaluation](CompletedEvaluation.lean) extends the original affine evaluation pairing to
structural-ring completions, retaining its value on every pair of original
classes. Restriction, coordinate detection, and global full-faithfulness are separate consumers.

[CompletedRestriction](CompletedRestriction.lean) proves compatibility of this pairing with every
inclusion of affine opens. [CompletedCoordinates](CompletedCoordinates.lean) identifies its original
quotient coordinates with the compatible-Hom comparison, and
[CompletedExt](CompletedExt.lean) detects a completed section by evaluating on restrictions
from a larger affine open. The last statement uses the actual restriction-image
spanning theorem, so it does not assume that an arbitrary affine inclusion is
principal.

[GluingIsomorphisms](GluingIsomorphisms.lean) combines original restricted-hom gluing and open-cover
isomorphism detection, retaining each original local comparison.

[LocalEpiDescent](LocalEpiDescent.lean) proves that local factorization equations through original
epimorphisms force overlap compatibility, then glues the actual global
factorization and retains its local maps.

[OpenCoverExt](OpenCoverExt.lean) detects equality of original module maps on
an open cover. [DiagramRestriction](DiagramRestriction.lean) transports whole
module-valued diagram maps through successive native open restrictions.
[DiagramGluing](DiagramGluing.lean) glues compatible local stage maps through
the same Hom sheaf; their transition equations are local, so the result is an
actual natural transformation. No quasicoherence or exactness of an ambient
target is required.

[DiagramFactorizationGluing](DiagramFactorizationGluing.lean) uses uniqueness
of whole factorization families on affine opens to force overlap compatibility
and glue the specified diagram factorization. Its uniqueness premise concerns
the whole compatible family; individual comparison components need not be
injective. The [bounded coherent reconstruction](../../Cohomology/GrothendieckExistence/BoundedCoherentReconstruction.lean)
and [formal modification comparison](../../Cohomology/GrothendieckExistence/FormalModificationBoundedComparison.lean)
consume these original restriction, gluing, and equality interfaces.
