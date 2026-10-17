# Descent of module sheaves

The objects are Mathlib's actual `X.Modules` with Mathlib's pullback functors
`Scheme.Modules.pullback f`, organized as the pseudofunctor
`Scheme.Modules.pullbackPseudofunctor : LocallyDiscrete Scheme.{u}ᵒᵖ ⥤ᵖ Cat.{u, u + 1}`.
Stack statements use Mathlib's `Pseudofunctor.IsPrestack` and `Pseudofunctor.IsStack`
(`Mathlib/CategoryTheory/Sites/Descent/`) and Mathlib's `Scheme.zariskiTopology`. This family
is the Zariski part (row F3) of the fppf stacks of row F6 in
[PICARD_PLAN.md](../../../../doc/PICARD_PLAN.md).

[Pseudofunctor](Pseudofunctor.lean):

- `pullbackPseudofunctor := Scheme.Modules.pseudofunctor.comp Adj.forget₁`, the left-adjoint
  part of Mathlib's pseudofunctor to `Adj Cat`; `pullbackPseudofunctor_obj` and
  `pullbackPseudofunctor_map_toFunctor` are `rfl`; `pullbackPseudofunctor_mapComp'_hom_app` and
  `_inv_app` express its composition isomorphisms through `pullbackComp` and `pullbackCongr`;
- object properties `pullbackPseudofunctor.isQuasicoherent` (Mathlib's
  `SheafOfModules.IsQuasicoherent`) and `pullbackPseudofunctor.isLocallyRankOne`
  (`Invertible.IsLocallyRankOne`), both closed under pullback and under isomorphism;
- `quasicoherentPseudofunctor` and `lineBundlePseudofunctor`, their full subpseudofunctors (all
  module morphisms). The latter is R5Lab's `Curves.Picard.EtaleDescent.lineBundles`.

[Substack](Substack.lean) is generic category theory (namespace
`CategoryTheory.Pseudofunctor.ObjectProperty`): for `P` closed under the functors `F.map`,
`descentDataForget` is fully faithful and `isPrestack_fullsubcategory` transfers `IsPrestack J`;
if `P` is also closed under isomorphisms, `isEquivalence_toDescentData_fullsubcategory`
transfers effectivity along a family `f` when `P` is local along `f`, and
`isStack_fullsubcategory` transfers `IsStack J` when `P` is local for the covering sieves of
`J`. It proves the statement of the TODO in Mathlib's
`Bicategory/Functor/Cat/ObjectProperty.lean`, with locality as an explicit hypothesis instead of
an `IsLocal` class, and with closure under isomorphisms added. Its intended owner is a
categorical descent family (Aglib `CategoryTheory/Sites/Descent/` or Mathlib).

[RestrictPullback](RestrictPullback.lean) proves that Mathlib's
`restrictFunctorIsoPullback` is compatible with `restrictFunctorComp`/`pullbackComp`
(`restrictFunctorIsoPullback_comp_hom_app`) and with `restrictFunctorCongr`/`pullbackCongr`.
Its intended owner is [Pullback](../../Modules/Pullback/README.md) (`OpenRestriction`) or Mathlib's
`Modules/Sheaf.lean`.

[Zariski](Zariski.lean):

- `isQuasicoherent_of_mem_zariskiTopology`, `isLocallyRankOne_of_mem_zariskiTopology`:
  both properties are local for Zariski covering sieves;
- `instance isPrestack_zariskiTopology`: morphisms of module sheaves glue along Zariski
  coverings; `isPrestack_quasicoherentPseudofunctor_zariskiTopology` and
  `isPrestack_lineBundlePseudofunctor_zariskiTopology` follow. For a jointly surjective
  family of open immersions, `fullyFaithfulToDescentDataOfOpenImmersion` glues with
  `InternalHom.existsUnique_restrictionHom`; `overlapRestrictIso_hom_app_restrictRestrictIso_hom`
  translates the descent-datum compatibility into restriction form;
- `isStack_zariskiTopology_of_opens` reduces `pullbackPseudofunctor.IsStack
  Scheme.zariskiTopology` to `toDescentData (fun i ↦ (U i).ι)` being an equivalence for every
  family of opens `U : ι → S.Opens` with `iSup U = ⊤` (`ι : Type (u + 1)`);
- `isStack_zariskiTopology_of_essSurj` reduces it, using the prestack instance, to essential
  surjectivity of the same functors;
- `pullbackPseudofunctor_pullHom_restrict`: restriction form of `pullHom` along an open
  immersion (coherence for comparing descent-datum transitions on nested opens; used by
  `pullbackPseudofunctor_pullHom_restrict'` and `cocycle_li` in ZariskiStack);
- `isStack_quasicoherentPseudofunctor_of_isStack`, `isStack_lineBundlePseudofunctor_of_isStack`:
  the module stack property gives the quasi-coherent and line-bundle stack properties.

[OpenCoverGluing](OpenCoverGluing.lean) (namespace `Scheme.Modules.OpenCoverGluing`) carries
out the effective gluing for a family of open immersions `f : ∀ i, X i ⟶ S` (`ι : Type u`)
and a descent datum `D` for `f`, with overlaps `Limits.pullback (f i) (f k)` (Stacks, Section 6.33,
Tag 00AK; Lemmas 6.33.2 and 6.33.3, Tags 00AL and 00AM). The statements are generic in the
family; instantiating descent-data statements at a concrete family of open subschemes made the
kernel exceed its deterministic limit.

- `transition`, `hom_eq_transition`, `transitionPullback`, `first`, `second`: the descent-datum
  morphism on the overlaps, in restriction and pullback form, and the S-module maps comparing
  the pushforwards of `D.obj i` and `D.obj k` on the overlap;
- `matching`, `gluedPresheaf`, `gluedPresheaf_isSheaf`, `glued : S.Modules`: matching families
  of sections form a sheaf of modules;
- `projection`, `toObj : (glued f D).restrict (f l) ⟶ D.obj l`, `projection_comp_first`,
  `isIso_second_app`, `projection_app_injective` (over `V ≤ (f l).opensRange` a matching family
  is determined by its `l`-component), `toObj_comm`, `phi`, `phi_comm_aux`, `phi_comm_pure`;
- `CategoryTheory.Pseudofunctor.DescentData.comm_of_overlap` (generic) and
  `exists_lift_pullback`: compatibility of morphisms of descent data can be checked on the
  overlaps;
- `descentData_comm_of`, `phiDescent`, `comparison : (toDescentData f).obj (glued f D) ⟶ D`;
- `isIso_toObj`, `comparisonIso`, `essSurj_toDescentData`, `isStackFor_ofArrows`: effective
  descent, given surjectivity of the projections;
- `ProjectionSurjective` and `isStack_zariskiTopology_of_projectionSurjective`, with
  `isStack_quasicoherentPseudofunctor_of_projectionSurjective` and
  `isStack_lineBundlePseudofunctor_of_projectionSurjective`. The proof applies
  `IsStack.of_precoverage`, reindexes each covering family by the points of `S`, and uses
  `IsStackFor.of_le` with the prestack instance.

[ZariskiStack](ZariskiStack.lean) proves the cocycle step and the three Zariski stack
instances (Stacks, Lemma 6.33.2, Tag 00AL, for the gluing of sections).

- `pullbackPseudofunctor_pullHom_restrict'`: restriction form of `pullHom` for arbitrary
  composites;
- the triple overlap `triple f l i k := Limits.pullback (snd f l i) (fst f i k)` with `tr₁`,
  `tr₂` and `tr₃ : triple f l i k ⟶ Limits.pullback (f l) (f k)`; `cocycle_restrict`,
  `cocycle_li`, `cocycle_ik`, `cocycle_lk` and `cocycle_transition`: `D.hom_comp` and
  `D.pullHom_hom` give the cocycle identity of the overlap transitions on the triple overlap;
  `cocycle_app` evaluates it on the sections over an open `Z` of the triple overlap;
- `transition_self` and `first_self`: on the diagonal overlap the transition is the canonical
  identification (`D.hom_self`, `Limits.fst_eq_snd_of_mono_eq`);
- `first_app_restrict`, `second_app_eq`, `second_app_restrict`, `comp_restrict`,
  `le_image_tr₂`, `comp_first_restrict_eq`: the matching step, compared after restriction to
  the part of `X i ×_S X k` covered by the triple overlap, where restriction is invertible over
  `V ≤ (f l).opensRange`;
- `projectionSurjective : ProjectionSurjective`, with preimage
  `s i := ((second f D l i).app V)⁻¹ ((first f D l i).app V t)`;
- instances `isStack_pullbackPseudofunctor_zariskiTopology`,
  `isStack_quasicoherentPseudofunctor_zariskiTopology` and
  `isStack_lineBundlePseudofunctor_zariskiTopology`.

The Zariski `IsStack` statements are therefore unconditional. `ProjectionSurjective` and the
conditional theorems of OpenCoverGluing remain as the assembly step that these instances use. No
quasi-coherence, finiteness or Noetherian hypothesis is used anywhere in this family. The fppf
layer (plan row F6) is developed in [Fppf](Fppf/README.md); its affine case is proved.

The `backward.*` options are scoped to the declarations that need them, each with a comment:
two lemmas in Pseudofunctor, one definition in Substack, four lemmas in Zariski,
`hom_eq_transition` and `comparisonIso` in OpenCoverGluing, and five lemmas in ZariskiStack
(`cocycle_restrict`, `hom_of_eq`, `first_app_restrict`, `comp_restrict`,
`comp_first_restrict_eq`). RestrictPullback needs none.

The focused consumer is
[AglibTest/AlgebraicGeometry/Descent/Modules/Zariski.lean](../../../../AglibTest/AlgebraicGeometry/Descent/Modules/Zariski.lean).
