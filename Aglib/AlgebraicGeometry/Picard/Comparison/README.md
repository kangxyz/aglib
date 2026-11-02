# Rigidification and the fppf comparison map

This family compares the Picard functors of [Picard](../README.md) with the rigidified functor
and with the fppf sheafification (plan row F7, target 4 of
[PICARD_PLAN.md](../../../../docs/PICARD_PLAN.md)). It follows Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Thm 2.5 with Def. 2.8 and Lemmas 2.9, 2.10 (pp. 18–20), and
[Stacks 0B9N](https://stacks.math.columbia.edu/tag/0B9N). The Picard-specific declarations live
in `AlgebraicGeometry.Scheme.RelativePicard`; the module-sheaf facts of Endomorphisms and the
O-connectedness of Injectivity in `AlgebraicGeometry.Scheme.Modules`. Generic category theory used
here lives in [Sites/Descent](../../../CategoryTheory/Sites/Descent/README.md) and
[Adjunction](../../../CategoryTheory/Adjunction/README.md). All objects are the committed Picard
functors, Mathlib's `Scheme.Modules.pullback`, and Mathlib's sheafification for
`Scheme.fppfTopology.over S`.

## Leaves

[Endomorphisms](Endomorphisms.lean), imported as
`Aglib.AlgebraicGeometry.Picard.Comparison.Endomorphisms`, has no hypothesis on the schemes:

- `pullback_map_globalScalarEndomorphism`: `(pullback f).map (globalScalarEndomorphism Y M a) =
  globalScalarEndomorphism X ((pullback f).obj M) (f.appTop a)`, with the pushforward form
  `pushforward_map_globalScalarEndomorphism`;
- `globalScalarEndomorphism_mul`, `_one`, `_conj`, and `globalScalarIso M a` for a global unit;
- `eq_unitMul_unitHomGlobalSectionsEquiv` (every endomorphism of the structure module is
  `unitMul` of its value at `1`), `unitIsoGlobalUnit` (the unit of an automorphism of the
  structure module), `globalScalarEndomorphism_injective_of_iso` (global functions act
  faithfully on a module isomorphic to the structure module);
- `exists_eq_globalScalarEndomorphism_of_isLocallyRankOne`: every endomorphism of a locally
  rank-one module sheaf is multiplication by a global function.

These are general module-sheaf facts. Their natural owners are
`Aglib.AlgebraicGeometry.Modules.Linear` and the [Invertible](../../Modules/Invertible/README.md)
family; they sit here because this family is their first consumer.

[Rigidified](Rigidified.lean), imported as `Aglib.AlgebraicGeometry.Picard.Comparison.Rigidified`,
assumes a section `o : S ⟶ X`, `ho : o ≫ p = 𝟙 S`:

- `RigidifiedPair p o ho T`: a `LineBundle (pullback p T.hom)` with an isomorphism
  `(pullback (originSection p o ho T)).obj L ≅ O_T` in `T.left.Modules` (Kleiman's `u` is its
  inverse); `RigidifiedPair.Iso` (bundle isomorphisms compatible with the rigidifications), the
  isomorphism setoid, and pullback of pairs `RigidifiedPair.map` along `f : T' ⟶ T`, through
  `pullbackComp`, `pullbackCongr` and `pullbackUnitIso`;
- `rigidifiedPicardFunctor p o ho : (Over S)ᵒᵖ ⥤ Type (u + 1)`, the isomorphism classes of pairs;
- Lemma 2.9: `RigidifiedPair.isoOfBundleIso` (pairs with isomorphic bundles are isomorphic),
  `rigidifiedClass_bijective`, `rigidifiedNormalizedIso : rigidifiedPicardFunctor p o ho ≅
  normalizedPicardFunctor p o ho ⋙ forget AddCommGrpCat` and, in Kleiman's form,
  `rigidifiedRelativeIso` onto `relativePicardFunctor p ⋙ forget AddCommGrpCat`, both sending
  `[(L, α)]` to the class of `L` (`_hom_app_mk`). Only the section is used;
- Lemma 2.10: `RigidifiedPair.Iso.eq_of_isIso_c` (with `[IsIso (pullback.snd p T.hom).c]`,
  isomorphisms of pairs over `T` are unique), `subsingleton_of_isIso_c`, `eq_refl_of_isIso_c`,
  and `eq_of_isProper_of_flat_of_geometricallyIntegral` for `S` locally Noetherian and `p`
  proper, flat, geometrically integral, from the F4 endpoint
  `isIso_c_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral`.

The functor laws of `rigidifiedPicardFunctor` follow from Lemma 2.9; no coherence of the
pullback pseudofunctor is used.

[Injectivity](Injectivity.lean), imported as
`Aglib.AlgebraicGeometry.Picard.Comparison.Injectivity`, has no hypothesis on `p` except in the
last item:

- `toFppfPicardSheaf_isLocallyInjective`, declared in [FppfSections](../FppfSections.lean), which
  Injectivity imports;
- `equalizerSieve_mem_of_toFppfPicardSheaf_app_eq_zero` and
  `exists_sieve_of_toFppfPicardSheaf_app_eq_zero`: a class with zero image in
  `Pic_{X/S,(fppf)}(T)` vanishes in `Pic(X ×_S U)` for all `U ⟶ T` in an fppf covering sieve;
- `FppfLocallyTrivialMemBaseImage p`: every fppf-locally trivial class on `X ×_S T` lies in the
  image of `Pic(T)`; `fppfLocallyTrivialMemBaseImage_iff_injective` proves it equivalent to
  injectivity of `toFppfPicardSheaf p` on every `T`, and
  `mono_toFppfPicardSheaf_of_fppfLocallyTrivialMemBaseImage` gives the monomorphism;
- the module form of O-connectedness, in `Scheme.Modules`: `isIso_unit_app_unit_of_isIso_c`
  (if `q.c` is an isomorphism, the adjunction unit `O_T ⟶ q_* q^* O_T` is one, through
  `unitToPushforwardObjUnit` and `pullbackUnitIso`) and, for `S` locally Noetherian and `p`
  proper, flat, geometrically integral,
  `isIso_unit_app_unit_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral`.

[LocallyTrivial](LocallyTrivial.lean), imported as
`Aglib.AlgebraicGeometry.Picard.Comparison.LocallyTrivial`, proves the fppf part of **Kleiman's
Thm 2.5(1)** (injectivity of the fppf comparison map) along Stacks 0B9M, without flat base change:

- graph morphisms `graph p h : W ⟶ X ×_S W` (`graphBase`, `graphObj`, `graphLift`,
  `graph_comp_familyScheme_map`, `graph_comp_graphLift`) and `familyMap p f`
  (the maps `X ×_S V i ⟶ X ×_S T`);
- `descentHomOfFamily` and `nonempty_iso_of_toDescentData_iso`: for an fppf prestack `F` on
  schemes, objects of `F (X ×_S T)` with isomorphic descent data for
  `F.restrictAlong (familyScheme p)` along `f` are isomorphic, when the `X ×_S V i` cover
  `X ×_S T`;
- `baseLineBundles S`, `familyLineBundles p` (line bundles on `T` and on `X ×_S T`, on `Over S`),
  `familyPullback p := CompTrans.ofNatTrans _ (familyProjection p)`, `IsTrivialLineBundle`;
- `bijective_familyPullback_map_of_isProper_of_flat_of_geometricallyIntegral` (universal
  O-connectedness makes `q_T^*` bijective on morphisms into trivial line bundles, through
  `Adjunction.bijective_map_of_isIso_unit_app`);
- `ofArrows_familyMap_mem`, `exists_familyPullback_iso_of_isProper_of_flat_of_geometricallyIntegral`
  (a line bundle on `X ×_S T` trivial on an fppf covering of `T` is `q_T^* N`);
- `fppfLocallyTrivialMemBaseImage_of_isProper_of_flat_of_geometricallyIntegral`,
  `toFppfPicardSheaf_app_injective_of_isProper_of_flat_of_geometricallyIntegral` and
  `mono_toFppfPicardSheaf_of_isProper_of_flat_of_geometricallyIntegral`, for `S` locally
  Noetherian and `p` proper, flat, with geometrically integral fibres.

[PullbackFullyFaithful](PullbackFullyFaithful.lean): for `p` proper, flat and geometrically integral
over a locally Noetherian base, and any `g : T ⟶ S`, the unit `N ⟶ q_* q^* N` is an isomorphism for
every line bundle `N` on `T` (`q = pullback.snd p g`;
`isIso_unit_app_pullback_snd_of_isLocallyRankOne_of_isProper_of_flat_of_geometricallyIntegral`), so
`q^*` is bijective on maps into line bundles
(`bijective_pullback_snd_map_of_isLocallyRankOne_of_isProper_of_flat_of_geometricallyIntegral`;
Kleiman, Lemma 2.7, p. 18). The trivial-target case is
`bijective_familyPullback_map_of_isProper_of_flat_of_geometricallyIntegral` above.

[Sheaf](Sheaf.lean), imported as `Aglib.AlgebraicGeometry.Picard.Comparison.Sheaf`:

- `isSeparated_relativePicardFunctor_of_isProper_of_flat_of_geometricallyIntegral` and
  `isSeparated_rigidifiedPicardFunctor_of_isProper_of_flat_of_geometricallyIntegral` (from the
  injectivity of the fppf comparison map). Separatedness fails without these hypotheses: for the
  fold map `S ⊔ S ⟶ S`, `P_{X/S}(T) ≅ Pic(T)`;
- `RigidifiedGluing p o ho`: compatible families of rigidified classes on fppf covering sieves
  have amalgamations (the gluing step of Stacks 0B9N). Under the hypotheses above it is
  equivalent to the sheaf property of the rigidified functor and to
  `IsIso (toFppfPicardSheaf p)`; it is proved in [Isomorphism](Isomorphism.lean).

[Gluing](Gluing.lean), imported as `Aglib.AlgebraicGeometry.Picard.Comparison.Gluing`, writes the
rigidification of a pulled-back pair through the pullback pseudofunctor: `originPullback`
(`CompTrans.ofNatTrans` at `originSectionNatTrans`), `pullbackPseudofunctor_square_app` (at
variable schemes), `originPullback_nat_hom_app`, `map_rigidification_hom` and
`mapComp'_unit_pullbackUnitIso`. The three bridges between the two presentations are stated
through `CompEq` (see below).

[GluingDescent](GluingDescent.lean), imported as
`Aglib.AlgebraicGeometry.Picard.Comparison.GluingDescent`, is the gluing of Stacks 0B9N:

- compatible rigidified pairs over a covering family form a descent datum for
  `familyLineBundles p` (`gluingDescentData`), provided the comorphism
  `O_Y ⟶ (X ×_S Y ⟶ Y)_* O` is an isomorphism for every `S`-scheme `Y`; its morphisms are the
  unique isomorphisms of pairs (Lemma 2.10);
- its compatibility with pullback is `RigidifiedPair.pairCompat_pullHom`, from the generic
  `CompTrans.rigCompat_pullHom`; `RigidifiedPair.Iso.pairCompat` and
  `RigidifiedPair.hom_eq_of_pairCompat_of_isIso_c` (Lemma 2.10 for such morphisms) are the two
  conversions between the presentations;
- the datum is transferred through graph morphisms to the maps `X ×_S V i ⟶ X ×_S T`
  (`familyDescentData`), and is then effective by the fppf stack of line bundles
  (`exists_iso_of_familyDescentData`), which gives
  `exists_lineBundle_of_rigidifiedPairs_of_isIso_c`.

[Isomorphism](Isomorphism.lean), imported as
`Aglib.AlgebraicGeometry.Picard.Comparison.Isomorphism`, proves **Kleiman's Thm 2.5(2) for the
fppf comparison map with a global section**, under the hypotheses above, with no gluing premise:

- `rigidifiedGluing_of_isIso_c` (under the comorphism hypothesis of Kleiman and Stacks 0B9N) and
  `rigidifiedGluing_of_isProper_of_flat_of_geometricallyIntegral`;
- `isSheaf_rigidifiedPicardFunctor_of_isProper_of_flat_of_geometricallyIntegral`;
- for `p` with a section (`IsSplitEpi p`):
  `isSheaf_relativePicardFunctor_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral`,
  `isIso_toFppfPicardSheaf_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral` and
  `relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral :
  relativePicardFunctor p ≅ (fppfPicardSheaf p).obj` (hom `toFppfPicardSheaf p`);
- for a chosen section `o`: `normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral` and
  `rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral`, compatible with
  `rigidifiedRelativeIso` and `rigidifiedNormalizedIso` (`_hom`, `_eq`).

The statements without `o` take `[IsSplitEpi p]`: their conclusions fail without a section (for
a conic over ℝ without a real point, `P(ℝ) ⟶ Pic_{(fppf)}(ℝ)` is multiplication by 2 on ℤ).

[RepresentableBy](RepresentableBy.lean), imported as
`Aglib.AlgebraicGeometry.Picard.Comparison.RepresentableBy`: under the hypotheses of Isomorphism
(`S` locally Noetherian, `p` proper, flat, geometrically integral fibres), a representation `e` of
`Pic_{X/S,(fppf)}` on locally Noetherian test schemes by `P` gives representations by the same `P`
of the normalized functor (`normalizedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral`), of
the rigidified functor (`rigidifiedRepresentableByOfIsProperOfFlatOfGeometricallyIntegral`), both
for a section `o`, and of `P_{X/S}` for `[IsSplitEpi p]`
(`relativeRepresentableByOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral`), each with its
`_homEquiv` formula, through the comparison isomorphisms (Kleiman, Thm 2.5(2), p. 18, with Def. 2.8
and Lemma 2.9, p. 19, for rigidified pairs; Stacks 0B9N).

**Presentations.** Pulled-back bundles have two presentations: Mathlib's pullback functors (in
`RigidifiedPair.map`) and the pullback pseudofunctor (in descent data). Equations between
composites written in the two presentations are compared through the regular definition
`CompEq f g h := f ≫ g = h` of
[Rigidification](../../../CategoryTheory/Sites/Descent/Rigidification.lean), whose instances the
kernel compares argument by argument; a direct comparison unfolds `CategoryStruct.comp`, which
has abbreviation hints, and was measured at several seconds of kernel time per declaration.

## Not yet proved

Target 4 of [PICARD_PLAN.md](../../../../docs/PICARD_PLAN.md) is closed. Not formalized:

- the Zariski and étale comparison maps and Kleiman's local-section clauses of Thm 2.5;
- the corollaries under Kleiman's hypothesis "`O_S ≅ f_*O_X` universally": only the gluing step
  has that form (`rigidifiedGluing_of_isIso_c`), because Thm 2.5(1) is formalized under the
  hypotheses above;
- the comparison with Kleiman's site of locally Noetherian `S`-schemes: the big fppf site
  `Over S` is used, as in [Fppf](../Fppf.lean).

## Consumers

The focused tests are `AglibTest.AlgebraicGeometry.Picard.Comparison.Endomorphisms`, `.Rigidified`,
`.Injectivity`, `.LocallyTrivial`, `.Sheaf`, `.Gluing` and `.Isomorphism` (with axiom guards).
Planned consumers are the normalized representability of target 6 and the representability
assembly (F17), which can use `normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral` and
`relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral`.

[UniversalRigidified](UniversalRigidified.lean) selects the actual universal
rigidified pair for the supplied representative. Pullbacks, original represented
class equations, unique rigidified comparisons and their coherence use that
same pair; classification is on the locally Noetherian represented tests.
