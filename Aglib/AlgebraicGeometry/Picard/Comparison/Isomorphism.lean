/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Comparison.GluingDescent

/-!
# The fppf comparison isomorphism with a global section (Kleiman, Thm 2.5(2))

Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 2.5(2), p. 18, and
[Stacks 0B9N](https://stacks.math.columbia.edu/tag/0B9N), for the fppf comparison map with a
global section. Let `p : X ⟶ S` have a section `o`.

* `rigidifiedGluing_of_isIso_c`: if the comorphism `O_T ⟶ (X ×_S T ⟶ T)_* O` is an isomorphism
  for every `S`-scheme `T`, every compatible family of isomorphism classes of rigidified pairs
  along an fppf covering sieve has an amalgamation (the gluing step of Stacks 0B9N): the
  representatives glue to a line bundle `L` on `X ×_S T`
  (`exists_lineBundle_of_rigidifiedPairs_of_isIso_c`), and the amalgamation is the class of `L`
  under Lemma 2.9 (`rigidifiedRelativeIso`).
* `rigidifiedGluing_of_isProper_of_flat_of_geometricallyIntegral`: the same for `S` locally
  Noetherian and `p` proper, flat, with geometrically integral fibres (universal
  O-connectedness, `isIso_c_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral`).
* Under these hypotheses: the rigidified Picard functor is an fppf sheaf
  (`isSheaf_rigidifiedPicardFunctor_of_isProper_of_flat_of_geometricallyIntegral`); for `p` with a
  section (`IsSplitEpi p`), so is `P_{X/S}`
  (`isSheaf_relativePicardFunctor_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral`) and
  the comparison map `P_{X/S} ⟶ Pic_{X/S,(fppf)}` is an isomorphism
  (`isIso_toFppfPicardSheaf_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral`,
  `relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral`); for a chosen section, the
  normalized and rigidified functors are `Pic_{X/S,(fppf)}`
  (`normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral`,
  `rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral`), compatibly with
  `toFppfPicardSheaf`, `rigidifiedRelativeIso` and `rigidifiedNormalizedIso`. The statements
  without `o` take `[IsSplitEpi p]`, since their conclusions fail without a section.

As in [Fppf](../Fppf.lean), the site is the big fppf site `Over S`; Kleiman's test schemes are
locally Noetherian, and the comparison with that site is not formalized here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite Pseudofunctor
open Over (homMkFamily homMkLeft)

namespace AlgebraicGeometry.Scheme.RelativePicard

universe u

open Scheme.Modules Scheme.Modules.Invertible

variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

/-- **The gluing of Stacks 0B9N.** If `O_T ⟶ (X ×_S T ⟶ T)_* O` is an isomorphism for every
`S`-scheme `T` (Kleiman's hypothesis "`O_S = f_* O_X` holds universally"), every compatible family
of isomorphism classes of rigidified pairs along an fppf covering sieve of `T` in `Over S` has an
amalgamation. -/
theorem rigidifiedGluing_of_isIso_c (hc : ∀ Y : Over S, IsIso (pullback.snd p Y.hom).c) :
    RigidifiedGluing p o ho := by
  intro T R hR x hx
  rw [GrothendieckTopology.mem_over_iff] at hR
  let g : ∀ a : (Sieve.overEquiv T R).arrows.category, a.obj.left ⟶ T.left := fun a ↦ a.obj.hom
  have hg : Sieve.ofArrows _ g ∈ Scheme.fppfTopology T.left := by
    rw [Sieve.ofArrows_category', Sieve.generate_sieve]
    exact hR
  have hmem : ∀ a, R.arrows (homMkFamily g a) := fun a ↦
    (Sieve.overEquiv_iff R a.obj.hom).mp a.property
  let P : ∀ a, RigidifiedPair p o ho (Over.mk (g a ≫ T.hom)) := fun a ↦
    Quotient.out (x (homMkFamily g a) (hmem a))
  have hxP : ∀ a, x (homMkFamily g a) (hmem a) = Quotient.mk _ (P a) := fun a ↦
    (Quotient.out_eq _).symm
  have hP : ∀ ⦃Y : Over S⦄ (q : Y ⟶ T) ⦃a₁ a₂ : (Sieve.overEquiv T R).arrows.category⦄
      (y₁ : Y ⟶ Over.mk (g a₁ ≫ T.hom)) (y₂ : Y ⟶ Over.mk (g a₂ ≫ T.hom)),
      y₁ ≫ homMkFamily g a₁ = q → y₂ ≫ homMkFamily g a₂ = q →
        Nonempty (RigidifiedPair.Iso (RigidifiedPair.map y₁ (P a₁))
          (RigidifiedPair.map y₂ (P a₂))) := by
    intro Y q a₁ a₂ y₁ y₂ hy₁ hy₂
    have h := hx y₁ y₂ (hmem a₁) (hmem a₂) (hy₁.trans hy₂.symm)
    rw [hxP, hxP] at h
    exact Quotient.exact h
  obtain ⟨L, hL⟩ := exists_lineBundle_of_rigidifiedPairs_of_isIso_c p o ho hc g hg P hP
  obtain ⟨t, ht⟩ : ∃ t, (rigidifiedRelativeIso p o ho).hom.app (op T) t =
      (QuotientAddGroup.mk (classOf _ L) :
        (familyPicardFunctor p).obj (op T) ⧸ baseImage p (op T)) :=
    ⟨_, Iso.inv_hom_id_app_apply _ _ _⟩
  have key : ∀ a, (rigidifiedPicardFunctor p o ho).map (homMkFamily g a).op t =
      x (homMkFamily g a) (hmem a) := by
    intro a
    rw [hxP]
    have h : (rigidifiedRelativeIso p o ho).hom.app (op (Over.mk (g a ≫ T.hom)))
        ((rigidifiedPicardFunctor p o ho).map (homMkFamily g a).op t) =
          (rigidifiedRelativeIso p o ho).hom.app (op (Over.mk (g a ≫ T.hom)))
            (Quotient.mk _ (P a)) := by
      rw [NatTrans.naturality_apply, ht, rigidifiedRelativeIso_hom_app_mk]
      exact (relativePicardFunctor_map_mk p (homMkFamily g a).op (classOf _ L)).trans
        (congrArg QuotientAddGroup.mk ((pullbackClass_classOf _ L).trans (Quotient.sound (hL a))))
    exact ((rigidifiedRelativeIso p o ho).app (op (Over.mk (g a ≫ T.hom)))).toEquiv.injective h
  refine ⟨t, fun Y f hf ↦ ?_⟩
  have hY : 𝟙 Y.left ≫ f.left ≫ T.hom = Y.hom := by
    rw [Category.id_comp]
    exact Over.w f
  have hY' : 𝟙 Y.left ≫ Y.hom = f.left ≫ T.hom := by
    rw [Category.id_comp]
    exact (Over.w f).symm
  have hf' : (Sieve.overEquiv T R).arrows f.left := by
    rw [Sieve.overEquiv_iff]
    have he : (Over.homMk (𝟙 Y.left) hY' : Over.mk (f.left ≫ T.hom) ⟶ Y) ≫ f = homMkLeft f := by
      ext
      exact Category.id_comp _
    have h := R.downward_closed hf (Over.homMk (𝟙 Y.left) hY' : Over.mk (f.left ≫ T.hom) ⟶ Y)
    rw [he] at h
    exact h
  let a : (Sieve.overEquiv T R).arrows.category := ⟨Over.mk f.left, hf'⟩
  let e : Y ⟶ Over.mk (g a ≫ T.hom) := Over.homMk (𝟙 Y.left) hY
  have hfe : e ≫ homMkFamily g a = f := by
    ext
    exact Category.id_comp _
  calc (rigidifiedPicardFunctor p o ho).map f.op t
      = (rigidifiedPicardFunctor p o ho).map (e ≫ homMkFamily g a).op t := by rw [hfe]
    _ = (rigidifiedPicardFunctor p o ho).map e.op
          ((rigidifiedPicardFunctor p o ho).map (homMkFamily g a).op t) := by
        rw [op_comp, Functor.map_comp_apply]
    _ = (rigidifiedPicardFunctor p o ho).map e.op (x (homMkFamily g a) (hmem a)) := by
        rw [key a]
    _ = (rigidifiedPicardFunctor p o ho).map (𝟙 Y).op (x f hf) :=
        hx e (𝟙 Y) (hmem a) hf (by rw [hfe, Category.id_comp])
    _ = x f hf := by rw [op_id, Functor.map_id_apply]

/-- **The gluing of Stacks 0B9N** for `S` locally Noetherian and `p` proper, flat, with
geometrically integral fibres. -/
theorem rigidifiedGluing_of_isProper_of_flat_of_geometricallyIntegral [IsLocallyNoetherian S]
    [IsProper p] [Flat p] [GeometricallyIntegral p] : RigidifiedGluing p o ho :=
  rigidifiedGluing_of_isIso_c p o ho fun Y ↦
    isIso_c_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral p Y.hom

/-- **Kleiman, Thm 2.5(2), sheaf form, for the fppf comparison map with a global section.** For
`S` locally Noetherian and `p` proper, flat, with geometrically integral fibres and with a
section, the rigidified Picard functor is an fppf sheaf: it is separated
(`isSeparated_rigidifiedPicardFunctor_of_isProper_of_flat_of_geometricallyIntegral`) and has
amalgamations (`rigidifiedGluing_of_isProper_of_flat_of_geometricallyIntegral`). -/
theorem isSheaf_rigidifiedPicardFunctor_of_isProper_of_flat_of_geometricallyIntegral
    [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    Presieve.IsSheaf (Scheme.fppfTopology.over S) (rigidifiedPicardFunctor p o ho) :=
  fun _ R hR ↦
    (isSeparated_rigidifiedPicardFunctor_of_isProper_of_flat_of_geometricallyIntegral p o ho R
      hR).isSheafFor (rigidifiedGluing_of_isProper_of_flat_of_geometricallyIntegral p o ho R hR)

/-- If `p` has a section (`IsSplitEpi p`) and the hypotheses of
`isSheaf_rigidifiedPicardFunctor_of_isProper_of_flat_of_geometricallyIntegral` hold, `P_{X/S}` is
an fppf sheaf of abelian groups (through Lemma 2.9, `rigidifiedRelativeIso`). -/
theorem isSheaf_relativePicardFunctor_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral
    [IsSplitEpi p] [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (relativePicardFunctor p) := by
  rw [Presheaf.isSheaf_iff_isSheaf_comp (Scheme.fppfTopology.over S) _
    (CategoryTheory.forget AddCommGrpCat.{u + 1}), isSheaf_iff_isSheaf_of_type]
  exact Presieve.isSheaf_iso (Scheme.fppfTopology.over S)
    (rigidifiedRelativeIso p (section_ p) (IsSplitEpi.id p))
    (isSheaf_rigidifiedPicardFunctor_of_isProper_of_flat_of_geometricallyIntegral p (section_ p)
      (IsSplitEpi.id p))

/-- **Kleiman, Thm 2.5(2), for the fppf comparison map with a global section** (Kleiman, *The
Picard scheme*, arXiv:math/0504020v1, Thm 2.5(2), p. 18;
[Stacks 0B9N](https://stacks.math.columbia.edu/tag/0B9N)). For `S` locally Noetherian and `p`
proper, flat, with geometrically integral fibres and with a section (`IsSplitEpi p`), the
comparison map `P_{X/S} ⟶ Pic_{X/S,(fppf)}` is an isomorphism. -/
theorem isIso_toFppfPicardSheaf_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral
    [IsSplitEpi p] [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    IsIso (toFppfPicardSheaf p) :=
  isIso_toSheafify (Scheme.fppfTopology.over S)
    (isSheaf_relativePicardFunctor_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral p)

/-- The comparison isomorphism `P_{X/S} ≅ Pic_{X/S,(fppf)}` of presheaves of abelian groups on
`Over S`, when `p` has a section (`IsSplitEpi p`). Its hom is `toFppfPicardSheaf p`. -/
def relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral [IsSplitEpi p]
    [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    relativePicardFunctor p ≅ (fppfPicardSheaf p).obj :=
  have := isIso_toFppfPicardSheaf_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral p
  asIso (toFppfPicardSheaf p)

theorem relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_hom [IsSplitEpi p]
    [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    (relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral p).hom =
      toFppfPicardSheaf p :=
  rfl

/-- The normalized Picard functor `T ↦ ker(o_T^*)` is `Pic_{X/S,(fppf)}`:
`quotientNormalizedIso` followed by the comparison isomorphism. -/
def normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral [IsLocallyNoetherian S] [IsProper p]
    [Flat p] [GeometricallyIntegral p] :
    normalizedPicardFunctor p o ho ≅ (fppfPicardSheaf p).obj :=
  have : IsSplitEpi p := IsSplitEpi.mk' ⟨o, ho⟩
  (quotientNormalizedIso p o ho).symm ≪≫
    relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral p

/-- The rigidified functor is `Pic_{X/S,(fppf)}` (values as types): `rigidifiedRelativeIso`
(Lemma 2.9) followed by the comparison isomorphism. -/
def rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral [IsLocallyNoetherian S] [IsProper p]
    [Flat p] [GeometricallyIntegral p] :
    rigidifiedPicardFunctor p o ho ≅
      (fppfPicardSheaf p).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1} :=
  have : IsSplitEpi p := IsSplitEpi.mk' ⟨o, ho⟩
  rigidifiedRelativeIso p o ho ≪≫
    Functor.isoWhiskerRight (relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral p)
      (CategoryTheory.forget AddCommGrpCat.{u + 1})

/-- Compatibility with Lemma 2.9: the rigidified comparison isomorphism is `rigidifiedRelativeIso`
followed by the comparison map. -/
theorem rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral_hom [IsLocallyNoetherian S]
    [IsProper p] [Flat p] [GeometricallyIntegral p] :
    (rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho).hom =
      (rigidifiedRelativeIso p o ho).hom ≫
        Functor.whiskerRight (toFppfPicardSheaf p) (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  rfl

/-- Compatibility with Lemma 2.9 in normalized form: the rigidified comparison isomorphism is
`rigidifiedNormalizedIso` followed by the normalized one. -/
theorem rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral_eq [IsLocallyNoetherian S]
    [IsProper p] [Flat p] [GeometricallyIntegral p] :
    rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho =
      rigidifiedNormalizedIso p o ho ≪≫
        Functor.isoWhiskerRight (normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho)
          (CategoryTheory.forget AddCommGrpCat.{u + 1}) := by
  ext T x
  rfl

end AlgebraicGeometry.Scheme.RelativePicard
