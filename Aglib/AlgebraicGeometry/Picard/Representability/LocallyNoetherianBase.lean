/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.BaseChangeRepresentableBy
public import Aglib.AlgebraicGeometry.Picard.Representability.FineStrata
public import Aglib.AlgebraicGeometry.ProjectiveSpace.ZariskiLocalClosedImmersion
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.BaseCover.FullSubcategory

/-!
# Representability of the fppf Picard functor over a locally Noetherian base

Let `S` be a locally Noetherian scheme and `f : X ⟶ S` a flat morphism with geometrically integral
fibres that is projective Zariski locally over `S`, with chosen embeddings
`E : ProjectiveSpace.ZariskiLocalClosedImmersion f`: open immersions `j a : Spec A_a ⟶ S`
covering `S` and closed immersions `c a : X ×_S Spec A_a ⟶ P(ι a)_{A_a}` over `Spec A_a`,
`ι a ≃ Fin (N a + 1)`.
This file proves Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 4.8(1), p. 27, in the fppf
form on locally Noetherian test schemes: `Pic_{X/S,(fppf)}` is represented by a locally Noetherian
`S`-scheme `P`, separated and locally of finite type over `S`, and `P ×_S Spec A_a` is the Picard
scheme of the closed subscheme `c a` of `P(ι a)_{A_a}` (`picardScheme`, Kleiman Thm 4.8 over the
Noetherian affine base `Spec A_a`)
(`exists_representableBy_fppfPicardSheaf_of_zariskiLocalClosedImmersion`).

The proof follows Kleiman, proof of Thm 4.8, p. 28: "By [EGA G, (0, 4.5.5), p. 106], it is a local
matter on `S` to represent a Zariski sheaf on the category of `S`-schemes. Moreover, it is also a
local matter on `S` to prove that an `S`-scheme is separated and locally of finite type." (EGA I
(1971), Ch. 0, (4.5.5), p. 106; citation not checked here.)

1. The restriction of `Pic_{X/S,(fppf)}` along `LocallyNoetherianOver.map (j a)` is the fppf
   Picard sheaf of `pullback.snd f (j a) = c a ≫ toSpec A_a (ι a)`
   (`locallyNoetherianFppfPicardSheafBaseChangeIso`), hence represented by the Picard scheme
   `E.chartPicardScheme a` of the chart (`E.chartPicardSchemeRepresentableBy a`, from
   `picardSchemeRepresentableBy` transported along `c_comp_toSpec` by `representableByOfEq`).
2. These representations glue along the base cover to `E.picardScheme`, which represents
   `Pic_{X/S,(fppf)}` on locally Noetherian test schemes (`E.picardSchemeRepresentableBy`;
   `SubfunctorCover.locallyNoetherianBaseCover` with the Zariski sheaf property
   `isZariskiSheaf_fppfPicardSheaf_forget`).
3. `E.picardScheme` is locally of finite type over `S`: its charts are the `Spec A_a`-schemes
   `E.chartPicardScheme a`, locally of finite type, followed by the open immersions `j a`
   (`E.locallyOfFiniteType_picardScheme`).
4. For every scheme `P` locally of finite type over `S` representing `Pic_{X/S,(fppf)}`,
   `P ×_S Spec A_a` represents the fppf Picard sheaf of `pullback.snd f (j a)`
   (`baseChangeRepresentableBy`), so it is isomorphic over `Spec A_a` to `E.chartPicardScheme a`,
   compatibly with the representations (`E.baseChangeIsoChartPicardScheme R a`,
   `E.baseChangeIsoChartPicardScheme_homEquiv`; Mathlib's `RepresentableBy.uniqueUpToIso`); for
   `E.picardScheme` this is `E.picardSchemeBaseChangeIso a`.
5. Separatedness is local on the target (Mathlib's `IsZariskiLocalAtTarget @IsSeparated`), and by 4
   the base change of `E.picardScheme` to each `Spec A_a` is separated, since the Picard scheme
   over `Spec A_a` is (`isSeparated_picardScheme`) (`E.isSeparated_picardScheme`).

The same conclusion, for all embeddings `E` at once, holds when `f` is only assumed H-projective
Zariski locally over `S` (`IsZariskiLocallyHProjective f`;
`exists_representableBy_fppfPicardSheaf_of_isZariskiLocallyHProjective`), since such `f` has
embeddings (`ZariskiLocalClosedImmersion.nonempty_of_isZariskiLocallyHProjective`).

Conditions: `S` locally Noetherian, `f` flat with geometrically integral fibres, and the data `E`;
no global embedding, no finiteness of the cover and no Noetherian hypothesis beyond `S` locally
Noetherian (each `A_a` is then Noetherian, `ZariskiLocalClosedImmersion.isNoetherianRing`). The
Hilbert-polynomial strata of Kleiman, Thm 4.8(2), which need `S` Noetherian and a global embedding,
and test schemes that are not locally Noetherian are not treated.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.LocalRepresentability

namespace AlgebraicGeometry

namespace Scheme.RelativePicard

variable {S X : Scheme.{u}}

/-- **Transport of a representation of `Pic_{X/S,(fppf)}` along an equality of morphisms**: for
`p = q`, a representation of the fppf Picard sheaf of `p` on locally Noetherian test schemes is one
of the fppf Picard sheaf of `q`. -/
def representableByOfEq {p q : X ⟶ S} (hpq : p = q) {Y : LocallyNoetherianOver S}
    (R : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Y) :
    ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf q).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Y :=
  hpq ▸ R

end Scheme.RelativePicard

namespace ProjectiveSpace.ZariskiLocalClosedImmersion

variable {S X : Scheme.{u}} {f : X ⟶ S} (E : ZariskiLocalClosedImmersion f) [IsLocallyNoetherian S]
  [Flat f] [GeometricallyIntegral f]

/-- The premise of the Picard scheme of the chart `a` holds: the fine strata of the closed
subscheme `c a` of `P(ι a)_{A_a}` are represented by H-quasi-projective schemes
(`Strata.fineStrataRepresentableByHQuasiProjective`). -/
theorem fineStrataRepresentableByHQuasiProjective (a : E.I) :
    RelativePicard.Strata.FineStrataRepresentableByHQuasiProjective (E.c a) (E.N a) (E.e a) :=
  RelativePicard.Strata.fineStrataRepresentableByHQuasiProjective (E.c a) (E.e a)

/-- **The Picard scheme of the chart `a`** (Kleiman, arXiv:math/0504020v1, Thm 4.8, over the
Noetherian affine base `Spec A_a`): the Picard scheme `picardScheme` of the closed subscheme
`c a : X ×_S Spec A_a ⟶ P(ι a)_{A_a}`, a locally Noetherian `Spec A_a`-scheme. -/
abbrev chartPicardScheme (a : E.I) : LocallyNoetherianOver (Spec (.of (E.A a))) :=
  RelativePicard.picardScheme (E.fineStrataRepresentableByHQuasiProjective a)

/-- **The restriction of `Pic_{X/S,(fppf)}` to the chart `a` is represented by the Picard scheme of
the chart**: on locally Noetherian `Spec A_a`-schemes, viewed over `S` through `j a`,
`Pic_{X/S,(fppf)}` is the fppf Picard sheaf of `pullback.snd f (j a) = c a ≫ toSpec A_a (ι a)`
(`locallyNoetherianFppfPicardSheafBaseChangeIso`), represented by `E.chartPicardScheme a`
(`picardSchemeRepresentableBy`). -/
def chartPicardSchemeRepresentableBy (a : E.I) :
    ((LocallyNoetherianOver.map (E.j a)).op ⋙ (locallyNoetherianOverInclusion S).op ⋙
      (RelativePicard.fppfPicardSheaf f).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy (E.chartPicardScheme a) :=
  (RelativePicard.representableByOfEq (E.c_comp_toSpec a)
    (RelativePicard.picardSchemeRepresentableBy
      (E.fineStrataRepresentableByHQuasiProjective a))).ofIso
    (RelativePicard.locallyNoetherianFppfPicardSheafBaseChangeIso f (E.j a)).symm

/-- The cover of `Pic_{X/S,(fppf)}` on locally Noetherian test schemes by the open subfunctors of
sections over test schemes landing in the charts `Spec A_a`, represented by the Picard schemes of
the charts. -/
abbrev picardBaseCover :
    SubfunctorCover ((locallyNoetherianOverInclusion S).op ⋙
      (RelativePicard.fppfPicardSheaf f).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  SubfunctorCover.locallyNoetherianBaseCover E.j E.covers E.chartPicardScheme
    E.chartPicardSchemeRepresentableBy

/-- **The Picard scheme over a locally Noetherian base** (Kleiman, arXiv:math/0504020v1,
Thm 4.8(1), p. 27): the locally Noetherian `S`-scheme glued from the Picard schemes of the charts
`Spec A_a`. -/
abbrev picardScheme : LocallyNoetherianOver S :=
  E.picardBaseCover.glued

/-- **The Picard scheme represents `Pic_{X/S,(fppf)}` on locally Noetherian test schemes**
(Kleiman, arXiv:math/0504020v1, Thm 4.8(1), p. 27, with fppf in place of étale; proof, p. 28). -/
def picardSchemeRepresentableBy :
    ((locallyNoetherianOverInclusion S).op ⋙ (RelativePicard.fppfPicardSheaf f).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy E.picardScheme :=
  E.picardBaseCover.representableByGlued (RelativePicard.isZariskiSheaf_fppfPicardSheaf_forget f)

-- Instance search for `IsZariskiLocalAtSource @LocallyOfFiniteType` (through `HasRingHomProperty`)
-- fails at instance transparency under the default `respectTransparency` setting.
set_option backward.isDefEq.respectTransparency false in
/-- **The Picard scheme is locally of finite type over `S`** (Kleiman, arXiv:math/0504020v1,
Thm 4.8(1), p. 27): its charts are the Picard schemes of the charts `Spec A_a`, locally of finite
type over `Spec A_a`, followed by the open immersions `j a`. -/
instance locallyOfFiniteType_picardScheme : LocallyOfFiniteType E.picardScheme.obj.hom :=
  E.picardBaseCover.prop_glued_hom @LocallyOfFiniteType fun (a : E.I) => by
    change LocallyOfFiniteType ((E.chartPicardScheme a).obj.hom ≫ E.j a)
    infer_instance

/-- **`P ×_S Spec A_a` is the Picard scheme of the chart `a`**, for every scheme `P` locally of
finite type over `S` representing `Pic_{X/S,(fppf)}` on locally Noetherian test schemes (Kleiman,
arXiv:math/0504020v1, Ex. 4.4, p. 27, and Answer 4.4, p. 65): the base change of `P` to `Spec A_a`
represents the fppf Picard sheaf of `pullback.snd f (j a)` on locally Noetherian test schemes
(`baseChangeRepresentableBy`), as does `E.chartPicardScheme a`, so they are isomorphic over
`Spec A_a` (Mathlib's `RepresentableBy.uniqueUpToIso`). -/
def baseChangeIsoChartPicardScheme {P : LocallyNoetherianOver S} [LocallyOfFiniteType P.obj.hom]
    (R : ((locallyNoetherianOverInclusion S).op ⋙ (RelativePicard.fppfPicardSheaf f).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) (a : E.I) :
    LocallyNoetherianOver.baseChange (E.j a) P ≅ E.chartPicardScheme a :=
  (RelativePicard.baseChangeRepresentableBy f (E.j a) P R).uniqueUpToIso
    (RelativePicard.representableByOfEq (E.c_comp_toSpec a)
      (RelativePicard.picardSchemeRepresentableBy (E.fineStrataRepresentableByHQuasiProjective a)))

/-- **The isomorphism `P ×_S Spec A_a ≅ E.chartPicardScheme a` identifies the representations**:
for a locally Noetherian `Spec A_a`-scheme `T`, a morphism `g : T ⟶ P ×_S Spec A_a` and its
composite with the isomorphism give the same section of the fppf Picard sheaf of
`pullback.snd f (j a)`. -/
theorem baseChangeIsoChartPicardScheme_homEquiv {P : LocallyNoetherianOver S}
    [LocallyOfFiniteType P.obj.hom]
    (R : ((locallyNoetherianOverInclusion S).op ⋙ (RelativePicard.fppfPicardSheaf f).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) (a : E.I)
    {T : LocallyNoetherianOver (Spec (.of (E.A a)))}
    (g : T ⟶ LocallyNoetherianOver.baseChange (E.j a) P) :
    (RelativePicard.representableByOfEq (E.c_comp_toSpec a)
      (RelativePicard.picardSchemeRepresentableBy
        (E.fineStrataRepresentableByHQuasiProjective a))).homEquiv
        (g ≫ (E.baseChangeIsoChartPicardScheme R a).hom) =
      (RelativePicard.baseChangeRepresentableBy f (E.j a) P R).homEquiv g := by
  set e := RelativePicard.baseChangeRepresentableBy f (E.j a) P R
  set e' := RelativePicard.representableByOfEq (E.c_comp_toSpec a)
    (RelativePicard.picardSchemeRepresentableBy (E.fineStrataRepresentableByHQuasiProjective a))
  have h : e'.homEquiv (E.baseChangeIsoChartPicardScheme R a).hom = e.homEquiv (𝟙 _) := by
    change e'.homEquiv (e'.homEquiv.symm (e.homEquiv (𝟙 _))) = e.homEquiv (𝟙 _)
    exact Equiv.apply_symm_apply _ _
  rw [e'.homEquiv_comp, h, ← e.homEquiv_comp, Category.comp_id]

/-- **`E.picardScheme ×_S Spec A_a` is the Picard scheme of the chart `a`**:
`baseChangeIsoChartPicardScheme` for `E.picardScheme`. -/
abbrev picardSchemeBaseChangeIso (a : E.I) :
    LocallyNoetherianOver.baseChange (E.j a) E.picardScheme ≅ E.chartPicardScheme a :=
  E.baseChangeIsoChartPicardScheme E.picardSchemeRepresentableBy a

/-- **The Picard scheme is separated over `S`** (Kleiman, arXiv:math/0504020v1, Thm 4.8(1), p. 27;
proof, p. 28): separatedness is local on `S`, and the base change to each chart `Spec A_a` is
isomorphic over `Spec A_a` to the Picard scheme of the chart, which is separated
(`isSeparated_picardScheme`). -/
instance isSeparated_picardScheme : IsSeparated E.picardScheme.obj.hom := by
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsSeparated) E.openCover fun (a : E.I) => ?_
  change IsSeparated (LocallyNoetherianOver.baseChange (E.j a) E.picardScheme).obj.hom
  rw [← Over.w (E.picardSchemeBaseChangeIso a).hom.hom]
  infer_instance

end ProjectiveSpace.ZariskiLocalClosedImmersion

namespace Scheme.RelativePicard

open ProjectiveSpace

variable {S X : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [Flat f] [GeometricallyIntegral f]

/-- **Representability of `Pic_{X/S,(fppf)}` over a locally Noetherian base** (Kleiman,
arXiv:math/0504020v1, Thm 4.8(1), p. 27, with fppf in place of étale, on locally Noetherian test
schemes; proof, p. 28). Let `S` be locally Noetherian and `f : X ⟶ S` flat with geometrically
integral fibres, with closed embeddings `E` into projective spaces over an affine open cover
`j a : Spec A_a ⟶ S` (projective Zariski locally over `S`). Then the fppf Picard functor is
represented on locally Noetherian test schemes by a locally Noetherian `S`-scheme `P` that is
separated and locally of finite type over `S`, and for every chart `a` the base change
`P ×_S Spec A_a` is isomorphic over `Spec A_a` to the Picard scheme `picardScheme h` of the closed
subscheme `c a` of `P(ι a)_{A_a}`, for the (unique) proof `h` of its premise, compatibly with the
representations: the representation of `P ×_S Spec A_a` (`baseChangeRepresentableBy`) is that of
`picardScheme h` (`picardSchemeRepresentableBy`, transported along `c a ≫ toSpec = pullback.snd f
(j a)` by `representableByOfEq`) through the isomorphism. The witnesses are `E.picardScheme` and
`E.picardSchemeRepresentableBy`. -/
theorem exists_representableBy_fppfPicardSheaf_of_zariskiLocalClosedImmersion
    (E : ZariskiLocalClosedImmersion f) :
    ∃ (P : LocallyNoetherianOver S)
      (R : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf f).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
      (_ : LocallyOfFiniteType P.obj.hom),
      IsSeparated P.obj.hom ∧
        ∀ (a : E.I) (h : Strata.FineStrataRepresentableByHQuasiProjective (E.c a) (E.N a) (E.e a)),
          ∃ i : LocallyNoetherianOver.baseChange (E.j a) P ≅ picardScheme h,
            ∀ {T : LocallyNoetherianOver (Spec (.of (E.A a)))}
              (g : T ⟶ LocallyNoetherianOver.baseChange (E.j a) P),
              (representableByOfEq (E.c_comp_toSpec a) (picardSchemeRepresentableBy h)).homEquiv
                  (g ≫ i.hom) =
                (baseChangeRepresentableBy f (E.j a) P R).homEquiv g :=
  ⟨E.picardScheme, E.picardSchemeRepresentableBy, inferInstance, inferInstance,
    fun a _ => ⟨E.picardSchemeBaseChangeIso a,
      fun g => E.baseChangeIsoChartPicardScheme_homEquiv E.picardSchemeRepresentableBy a g⟩⟩

/-- **Representability of `Pic_{X/S,(fppf)}` over a locally Noetherian base, for `f` H-projective
Zariski locally over `S`** (Kleiman, arXiv:math/0504020v1, Thm 4.8(1), p. 27, with fppf in place
of étale, on locally Noetherian test schemes; proof, p. 28). Let `S` be locally Noetherian and
`f : X ⟶ S` flat with geometrically integral fibres such that every point of `S` lies in an affine
open over which `f` is H-projective (`IsZariskiLocallyHProjective f`). Then the fppf Picard functor
is represented on locally Noetherian test schemes by a locally Noetherian `S`-scheme `P` that is
separated and locally of finite type over `S`, and for all closed embeddings `E` into projective
spaces over an affine open cover of `S` and every chart `a` of `E`, `P ×_S Spec A_a` is isomorphic
over `Spec A_a` to the Picard scheme `picardScheme h` of the closed subscheme `c a` of
`P(ι a)_{A_a}`, compatibly with the representations. -/
theorem exists_representableBy_fppfPicardSheaf_of_isZariskiLocallyHProjective
    [IsZariskiLocallyHProjective f] :
    ∃ (P : LocallyNoetherianOver S)
      (R : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf f).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
      (_ : LocallyOfFiniteType P.obj.hom),
      IsSeparated P.obj.hom ∧
        ∀ (E : ZariskiLocalClosedImmersion f) (a : E.I)
          (h : Strata.FineStrataRepresentableByHQuasiProjective (E.c a) (E.N a) (E.e a)),
          ∃ i : LocallyNoetherianOver.baseChange (E.j a) P ≅ picardScheme h,
            ∀ {T : LocallyNoetherianOver (Spec (.of (E.A a)))}
              (g : T ⟶ LocallyNoetherianOver.baseChange (E.j a) P),
              (representableByOfEq (E.c_comp_toSpec a) (picardSchemeRepresentableBy h)).homEquiv
                  (g ≫ i.hom) =
                (baseChangeRepresentableBy f (E.j a) P R).homEquiv g := by
  obtain ⟨E⟩ := ZariskiLocalClosedImmersion.nonempty_of_isZariskiLocallyHProjective f
  exact ⟨E.picardScheme, E.picardSchemeRepresentableBy, inferInstance, inferInstance,
    fun E' a _ => ⟨E'.baseChangeIsoChartPicardScheme E.picardSchemeRepresentableBy a,
      fun g => E'.baseChangeIsoChartPicardScheme_homEquiv E.picardSchemeRepresentableBy a g⟩⟩

end Scheme.RelativePicard

end AlgebraicGeometry
