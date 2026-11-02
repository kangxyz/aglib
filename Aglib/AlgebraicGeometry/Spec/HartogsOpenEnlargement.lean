/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Isomorphisms
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSectionsGlobal
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.QuasiCoherent
public import Aglib.AlgebraicGeometry.Spec.SplitAdicSections

/-! # Enlarging an actual Hartogs open

The quasicoherent unit for a quasi-compact open immersion into an affine scheme
is detected on original global sections. Consequently the original scalar map
remains bijective on every larger open. No reducedness, density, normality, or
domain hypothesis is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- The actual structure-module unit of a quasi-compact Hartogs open is an
isomorphism, detected by its original global scalar map. -/
theorem isIso_unitToPushforward_of_hartogs_open
    (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens)
    [QuasiCompact U.ι]
    (hU : Function.Bijective (affineScalarMap U.ι)) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit U.ι.toRingCatSheafHom) := by
  let η : (Spec (.of A)).Modules := SheafOfModules.unit (Spec (.of A)).ringCatSheaf
  let : η.IsQuasicoherent := Modules.isQuasicoherent_unit _
  let : (SheafOfModules.unit U.toScheme.ringCatSheaf).IsQuasicoherent :=
    Modules.isQuasicoherent_unit _
  let : ((Modules.pushforward U.ι).obj
      (SheafOfModules.unit U.toScheme.ringCatSheaf)).IsQuasicoherent :=
    Modules.QuasiCoherent.quasicoherent_pushforward_open U.ι _
  let f : η ⟶ (Modules.pushforward U.ι).obj
      (SheafOfModules.unit U.toScheme.ringCatSheaf) :=
    SheafOfModules.unitToPushforwardObjUnit U.ι.toRingCatSheafHom
  have htop : Function.Bijective U.ι.appTop :=
    (Function.Bijective.of_comp_iff _
      ((ConcreteCategory.isIso_iff_bijective (ΓSpecIso (.of A)).inv).mp inferInstance)).mp hU
  let : IsIso ((moduleSpecΓFunctor (R := .of A)).map f) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr htop
  exact Modules.QuasiCoherent.affine_isIso_of_globalSections (.of A) f

/-- Restriction from a larger open to the original Hartogs open is the
original presheaf restriction, and is an isomorphism. -/
theorem isIso_restriction_to_hartogs_open
    (A : Type u) [CommRing A] (U V : (Spec (.of A)).Opens)
    [QuasiCompact U.ι] (hUV : U ≤ V)
    (hU : Function.Bijective (affineScalarMap U.ι)) :
    IsIso ((Spec (.of A)).presheaf.map (homOfLE hUV).op) := by
  let f : (SheafOfModules.unit (Spec (.of A)).ringCatSheaf :
      (Spec (.of A)).Modules) ⟶ (Modules.pushforward U.ι).obj
      (SheafOfModules.unit U.toScheme.ringCatSheaf) :=
    SheafOfModules.unitToPushforwardObjUnit U.ι.toRingCatSheafHom
  let : IsIso f := isIso_unitToPushforward_of_hartogs_open A U hU
  have hf : IsIso (U.ι.app V) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact (ConcreteCategory.isIso_iff_bijective (Modules.Hom.app f V)).mp inferInstance
  have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = U := by
    simp only [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι,
      inf_eq_left.mpr hUV]
  have hh : U.ι.app V =
      (Spec (.of A)).presheaf.map (homOfLE hUV).op ≫
        (Spec (.of A)).presheaf.map (eqToHom he).op := by
    rw [Opens.ι_app, ← Functor.map_comp]
    rfl
  rw [hh] at hf
  exact (isIso_comp_right_iff
    ((Spec (.of A)).presheaf.map (homOfLE hUV).op)
    ((Spec (.of A)).presheaf.map (eqToHom he).op)).mp hf

/-- The original ambient scalar restriction remains bijective on every
larger open; the smaller open alone must be quasi-compact. -/
theorem hartogsScalarMap_bijective_of_le
    (A : Type u) [CommRing A] (U V : (Spec (.of A)).Opens)
    [QuasiCompact U.ι] (hUV : U ≤ V)
    (hU : Function.Bijective (affineScalarMap U.ι)) :
    Function.Bijective (hartogsScalarMap A V) := by
  let r := (Spec (.of A)).presheaf.map (homOfLE hUV).op
  let : IsIso r := isIso_restriction_to_hartogs_open A U V hUV hU
  have hr : Function.Bijective r :=
    (ConcreteCategory.isIso_iff_bijective r).mp inferInstance
  have hcomp : r.hom.comp (hartogsScalarMap A V) = hartogsScalarMap A U := by
    change (((ΓSpecIso (.of A)).inv ≫
      (Spec (.of A)).presheaf.map (homOfLE le_top).op) ≫ r).hom = _
    simp only [Category.assoc, r, ← Functor.map_comp]
    rfl
  have hsmall : Function.Bijective (hartogsScalarMap A U) := by
    rw [← affineScalarMap_topIso U]
    exact ((ConcreteCategory.isIso_iff_bijective U.topIso.hom).mp inferInstance).comp hU
  apply (Function.Bijective.of_comp_iff' hr _).mp
  change Function.Bijective (r.hom.comp (hartogsScalarMap A V))
  rw [hcomp]
  exact hsmall

/-- The same enlargement statement on the original restricted scheme's
global sections, with its original affine scalar map. -/
theorem affineScalarMap_bijective_of_hartogs_open_le
    (A : Type u) [CommRing A] (U V : (Spec (.of A)).Opens)
    [QuasiCompact U.ι] (hUV : U ≤ V)
    (hU : Function.Bijective (affineScalarMap U.ι)) :
    Function.Bijective (affineScalarMap V.ι) := by
  have h := hartogsScalarMap_bijective_of_le A U V hUV hU
  rw [← affineScalarMap_topIso V] at h
  exact (Function.Bijective.of_comp_iff'
    ((ConcreteCategory.isIso_iff_bijective V.topIso.hom).mp inferInstance) _).mp h

end AlgebraicGeometry.Scheme
