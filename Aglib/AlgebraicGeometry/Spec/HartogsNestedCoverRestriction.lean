/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.HartogsCoverRestriction

/-! # Literal nested-open restriction of the original finite flat cover

The native `Opens.isoOfLE` identifies the source of the original `homOfLE`
with the literal inverse-image open. Its original composition equation
transports the structure unit, and the actual cover restriction theorem
then applies without choosing any replacement cover.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

private theorem structureUnit_isIso_of_schemeIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  let k : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶
      (Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  change IsIso k
  apply Modules.Hom.isIso_iff_isIso_app.mpr
  intro T
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact (ConcreteCategory.isIso_iff_bijective (f.app T)).mp inferInstance

/-- The native nested-open isomorphism retains the original structure unit
on the literal inverse image, rather than replacing that open by an equal one. -/
theorem isIso_structureUnit_nested_hartogs_open
    (A : Type u) [CommRing A] (U V : (Spec (.of A)).Opens)
    [QuasiCompact U.ι] [QuasiCompact V.ι] (hUV : U ≤ V)
    (hU : Function.Bijective (affineScalarMap U.ι)) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit
      (V.ι ⁻¹ᵁ U).ι.toRingCatSheafHom) := by
  let e := Opens.isoOfLE hUV
  let j := (Spec (.of A)).homOfLE hUV
  let : IsIso (SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom) :=
    structureUnit_isIso_of_schemeIso e.hom
  let : IsIso (SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom) :=
    Modules.isIso_structureUnit_homOfLE_hartogs A U V hUV hU
  have hc := Modules.unitToPushforwardObjUnit_comp e.hom j
  have hi : IsIso (SheafOfModules.unitToPushforwardObjUnit
      (e.hom ≫ j).toRingCatSheafHom) := by
    rw [← hc]
    infer_instance
  have he : e.hom ≫ j = (V.ι ⁻¹ᵁ U).ι := by
    apply (cancel_mono V.ι).mp
    simp only [Category.assoc, j, homOfLE_ι]
    exact Opens.isoOfLE_hom_ι hUV
  exact (congrArg (fun f : (V.ι ⁻¹ᵁ U).toScheme ⟶ V.toScheme =>
    IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) he).mp hi

/-- The actual ring restriction of the original cover to the nested open
is bijective. The finite flat cover is only assumed to exist over V. -/
theorem cover_nested_restriction_appTop_bijective
    (A : Type u) [CommRing A] (U V : (Spec (.of A)).Opens)
    [QuasiCompact U.ι] [QuasiCompact V.ι] (hUV : U ≤ V)
    (hU : Function.Bijective (affineScalarMap U.ι))
    {W : Scheme.{u}} (p : W ⟶ V) [IsFinite p] [Flat p]
    [LocallyOfFinitePresentation p] :
    Function.Bijective (p ⁻¹ᵁ (V.ι ⁻¹ᵁ U)).ι.appTop := by
  let : IsIso (SheafOfModules.unitToPushforwardObjUnit
      (V.ι ⁻¹ᵁ U).ι.toRingCatSheafHom) :=
    isIso_structureUnit_nested_hartogs_open A U V hUV hU
  exact cover_restriction_appTop_bijective_of_structureUnit p (V.ι ⁻¹ᵁ U)

/-- The original selected pullback used by finite-etale base change retains
the same bijective section restriction. Its comparison is the native
pullback isomorphism of the literal inverse-image square. -/
theorem cover_homOfLE_pullback_fst_appTop_bijective
    (A : Type u) [CommRing A] (U V : (Spec (.of A)).Opens)
    [QuasiCompact U.ι] [QuasiCompact V.ι] (hUV : U ≤ V)
    (hU : Function.Bijective (affineScalarMap U.ι))
    {W : Scheme.{u}} (p : W ⟶ V) [IsFinite p] [Flat p]
    [LocallyOfFinitePresentation p] :
    Function.Bijective (pullback.fst p ((Spec (.of A)).homOfLE hUV)).appTop := by
  let O := V.ι ⁻¹ᵁ U
  let e := Opens.isoOfLE hUV
  let j := (Spec (.of A)).homOfLE hUV
  have he : e.hom ≫ j = O.ι := by
    apply (cancel_mono V.ι).mp
    simp only [Category.assoc, j, homOfLE_ι]
    exact Opens.isoOfLE_hom_ι hUV
  have H : IsPullback (p ⁻¹ᵁ O).ι ((p ∣_ O) ≫ e.hom) p j := by
    apply (isPullback_morphismRestrict p O).flip.of_iso
      (Iso.refl _) (Iso.refl _) e (Iso.refl _)
    · simp
    · simp
    · simp
    · simpa only [Iso.refl_hom, Category.comp_id] using he.symm
  let : IsIso (p ⁻¹ᵁ O).ι.appTop :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (cover_nested_restriction_appTop_bijective A U V hUV hU p)
  have hc : (pullback.fst p j).appTop ≫ H.isoPullback.hom.appTop =
      (p ⁻¹ᵁ O).ι.appTop := by
    rw [← Hom.comp_appTop, H.isoPullback_hom_fst]
  have hi : IsIso ((pullback.fst p j).appTop ≫ H.isoPullback.hom.appTop) := by
    rw [hc]
    infer_instance
  let : IsIso (pullback.fst p j).appTop :=
    IsIso.of_isIso_comp_right _ H.isoPullback.hom.appTop
  exact (ConcreteCategory.isIso_iff_bijective (pullback.fst p j).appTop).mp inferInstance

end AlgebraicGeometry.Scheme
