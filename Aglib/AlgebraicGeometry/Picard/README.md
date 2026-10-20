# Picard functors over a base

The owner is `AlgebraicGeometry.Scheme.RelativePicard`. For a morphism of schemes
`p : X ⟶ S` the family constructs presheaves of additive commutative groups on
`Over S`, with values in `AddCommGrpCat.{u + 1}` for `S X : Scheme.{u}`. Every value
is an actual `Scheme.Modules.Invertible.PicardGroup`, and every map is the proved
additive pullback `Scheme.Modules.Invertible.PullbackTensor.Local.pullbackHom`; no
tensor-pullback or other theorem-family parameter is used. The functors are defined on
all of `Over S`, nonreduced and non-Noetherian test schemes included. The plan in
[PICARD_PLAN.md](../../../docs/PICARD_PLAN.md) restricts later representability
statements, not these definitions.

[Presheaf](Presheaf.lean), imported as `Aglib.AlgebraicGeometry.Picard.Presheaf`,
has no hypothesis on `p`:

- `picardFunctor : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1}` is `Y ↦ Pic(Y)`;
- `familyScheme p : Over S ⥤ Scheme.{u}` is `T ↦ pullback p T.hom`, with Mathlib's
  `pullback.map p T.hom p T'.hom (𝟙 X) f.left (𝟙 S)` as transition maps;
  `familyProjection p` is the natural `pullback.snd`;
- `basePicardFunctor S := (Over.forget S).op ⋙ picardFunctor` is `T ↦ Pic(T)`, and
  `familyPicardFunctor p := (familyScheme p).op ⋙ picardFunctor` is
  `T ↦ Pic(X ×_S T)`, Kleiman's absolute functor `Pic_X` (Kleiman, arXiv:math/0504020v1,
  Def. 2.1, p. 16);
- `basePullback p : basePicardFunctor S ⟶ familyPicardFunctor p` is pullback along
  `pullback.snd`;
- `relativePicardFunctor p` is `P_{X/S}(T) = Pic(X ×_S T) / Pic(T)` (Kleiman, Def. 2.2,
  p. 17), the pointwise quotient by `baseImage p T`, the range of the base pullback, with
  transition maps `QuotientAddGroup.map`; `quotientProjection p` is the natural quotient
  map, surjective with kernel `baseImage p T` (`quotientProjection_app_ker`).

[Normalized](Normalized.lean), imported as `Aglib.AlgebraicGeometry.Picard.Normalized`,
assumes a section `o : S ⟶ X` with `ho : o ≫ p = 𝟙 S`, and nothing else:

- `originSection p o ho T = pullback.lift (T.hom ≫ o) (𝟙 T.left) _ : T.left ⟶ pullback p T.hom`,
  natural as `originSectionNatTrans`, with `originSectionNatTrans_familyProjection`;
- `originRestriction p o ho : familyPicardFunctor p ⟶ basePicardFunctor S` is pullback along
  the origin sections; `basePullback_originRestriction` proves that it retracts the base
  pullback, so `basePullback_app_injective` holds;
- `normalizedPicardFunctor p o ho` is the pointwise kernel `T ↦ ker(o_T^*)`
  (`normalizedSubgroup`), with `normalizedInclusion`;
- `quotientNormalizedIso p o ho : relativePicardFunctor p ≅ normalizedPicardFunctor p o ho`
  sends `[L]` to `L - pr₂^*(o_T^* L)`; `quotientNormalizedIso_inv` identifies its inverse
  with `normalizedInclusion ≫ quotientProjection`. The additive splitting lemma is
  `RelativePicard.Split.quotientEquiv`.

[Fppf](Fppf.lean), imported as `Aglib.AlgebraicGeometry.Picard.Fppf`, has no hypothesis
on `p`. `fppfPicardSheaf p` is `Pic_{X/S,(fppf)}`, Mathlib's
`(presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
(relativePicardFunctor p)`, with the plus-plus instance from
`Mathlib.CategoryTheory.Sites.LeftExact`. `toFppfPicardSheaf p` is the sheafification
unit `toSheafify`, and `fppfPicardSheafHomEquiv` with `fppfPicardSheafHomEquiv_apply`
records the universal property for fppf sheaves of abelian groups. For a class
`a : PicardGroup T`, `vanishingSieve a` is the sieve of morphisms `f` with
`pullbackClass f a = 0`. Every class vanishes on a Zariski covering by trivializing opens
(`vanishingSieve_mem_zariskiTopology`), hence on an fppf covering
(`vanishingSieve_mem_fppfTopology`). So the instances
`quotientProjection_isLocallyInjective` and `quotientProjection_isLocallySurjective` hold
for `Scheme.fppfTopology.over S`, `isIso_presheafToSheaf_map_quotientProjection` makes the
sheafified quotient map invertible, and `fppfFamilyPicardSheafIso p` identifies the fppf
sheafification of `familyPicardFunctor p` with `fppfPicardSheaf p`; its forward map is the
sheafification of `quotientProjection p` (`fppfFamilyPicardSheafIso_hom`)
(Kleiman, Def. 2.2, p. 17, and the remark after it).
[Stacks 0B9L](https://stacks.math.columbia.edu/tag/0B9L) defines the Picard functor as the
set-valued fppf sheafification of `T ↦ Pic(X_T)`; here sheafification is taken in
`AddCommGrpCat.{u + 1}`. The local-bijectivity criterion is Mathlib's
`GrothendieckTopology.WEqualsLocallyBijective` instance for `AddCommGrpCat.{u + 1}`.

[Comparison](Comparison/README.md) adds the rigidified functor with Kleiman's Lemmas
2.9 and 2.10. It also reduces the injectivity of `toFppfPicardSheaf` (Thm 2.5(1)) to the
equivalent premise `FppfLocallyTrivialMemBaseImage`.

Not yet proved here:

- that premise under universal O-connectedness;
- the bijectivity of `toFppfPicardSheaf` with a section (target 4 of the plan);
- representability.

Source provenance: `R5Lab.AlgebraicGeometry.Curves.RelativePicard` and
`RelativePicard/Group.lean`. Retained names: `basePicardFunctor`, `familyPicardFunctor`,
`basePullback`, `originSection`, `originRestriction`, `basePullback_originRestriction`,
`normalizedInclusion`, `quotientNormalizedEquiv`, `quotientNormalizedIso`,
`quotientProjection` and `Split`; `basePullback_injective` is now
`basePullback_app_injective`.
The R5Lab `Type (u + 1)`-valued `basePicardFunctor`, `familyPicardFunctor` and
`normalizedClassFunctor` are the composites of the presheaves here with
`forget AddCommGrpCat`, with definitionally equal values on objects. Their transition
maps agree only propositionally: R5Lab's `familyMap` is `pullback.lift fst (snd ≫ a)`,
whereas `familyScheme` uses `pullback.map`, so retargeting R5Lab needs an explicit
comparison of maps. R5Lab's
`basePicardGroupFunctor`, `familyPicardGroupFunctor`, `normalizedGroupFunctor` and
`relativeQuotientGroupFunctor` correspond to `basePicardFunctor`, `familyPicardFunctor`,
`normalizedPicardFunctor` and `relativePicardFunctor`. The R5Lab relative quotient used
the section to define its transition maps; here they are induced by the base pullback
and need no section. R5Lab's `RelativeDivisors.familyMap` is replaced by
`pullback.map`, and its `ModuleTensorPullback` parameter by the proved `pullbackHom`.

Lower prerequisites are the [Invertible](../Modules/Invertible/README.md) family
(`PicardGroup`, `pullbackClass`, `PullbackTensor.Local.pullbackHom`), Mathlib's
`pullback.map`, `Scheme.fppfTopology`, `GrothendieckTopology.over` and sheafification.
The present consumer is the focused test `AglibTest.AlgebraicGeometry.Picard.Functors`;
`AglibTest.AlgebraicGeometry.Picard.Interfaces` records the M0 interface probes.
Planned consumers are the comparison and rigidification layer (plan F7), the
representability assembly (F17) and the R5Lab `Curves.RelativePicard` retargeting.

The [Relative compatibility guide](Relative/README.md) identifies the incoming
class/group functors and their actual transition maps with the native Picard
presheaves. Original schemes and test schemes may be arbitrary, including
nonreduced and non-Noetherian tests. The proper-flat sheaf comparison separately
keeps its locally Noetherian original base and geometrically integral fibres.
The [curve representability interface](../Curves/RelativePicard/Representability.lean)
remains an input to the prescribed-origin genus-one construction.
[PowerRoot](PowerRoot.lean), [PowerDescent](PowerDescent.lean) and
[FrameTorsor](FrameTorsor.lean) describe actual root, descent and frame objects.
