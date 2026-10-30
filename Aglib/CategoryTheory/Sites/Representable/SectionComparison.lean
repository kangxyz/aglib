/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.SourceSection
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Original coefficient comparisons along an actual section

The original composition and identity comparisons normalize the actual
coefficient maps, then the same exact Ext transfer proves the section formula.
No final section coefficient/cohomology square is supplied as a premise. The
current native instance is the original roots coefficient comparison.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Functor

universe uC vC uD vD eC eD

section Identity

variable {C : Type uC} [Category.{vC} C] (F : C ⥤ C) {K : C ⥤ C}

/-- Actual composition/unit equations identify the original identity coefficient map. -/
theorem coefficientIso_identity (i : F ≅ 𝟭 C) (c : K ≅ F ⋙ F) (A : C)
    (j : K.obj A ⟶ F.obj A) (q : F.obj A ≅ A)
    (hcomp : c.hom.app A ≫ F.map q.hom ≫ q.hom = j ≫ q.hom)
    (hunit : c.hom.app A ≫ F.map (i.hom.app A) = j) :
    q.hom = i.hom.app A := by
  let : F.Faithful := Functor.Faithful.of_iso i.symm
  apply F.map_injective
  apply (cancel_epi (c.hom.app A)).mp
  have hq : c.hom.app A ≫ F.map q.hom = j := by
    apply (cancel_mono q.hom).mp
    simpa only [Category.assoc] using hcomp
  exact hq.trans hunit.symm

end Identity

section Coefficients

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {F : C ⥤ D} {H : D ⥤ C} {K : C ⥤ C}

/-- Whole original section coefficient contraction, derived from composition and identity. -/
theorem sectionCoefficient_of_composition (c : K ≅ F ⋙ H) (i : K ≅ 𝟭 C)
    {A : C} {B : D} (q : F.obj A ≅ B) (r : H.obj B ≅ A) (k : K.obj A ≅ A)
    (hcomp : c.hom.app A ≫ H.map q.hom ≫ r.hom = k.hom)
    (hid : k.hom = i.hom.app A) :
    H.map q.hom ≫ r.hom = (sourceSectionIso c i).hom.app A := by
  apply (cancel_epi (c.hom.app A)).mp
  simpa only [sourceSectionIso_hom_app, Iso.hom_inv_id_app_assoc, Category.assoc] using
    hcomp.trans hid

end Coefficients

section Ext

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasExt.{eC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasExt.{eD} D]
  (F : C ⥤ D) (H : D ⥤ C) [H.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H] (K : C ⥤ C)
  (c : K ≅ F ⋙ H) (i : K ≅ 𝟭 C)
  {U : C} {V : D} (sH : U ⟶ H.obj V)

/-- The same original maps give the entire Ext section formula in every existing degree. -/
theorem extSectionPullback_coefficientIso
    {A : C} {B : D} (q : F.obj A ≅ B) (r : H.obj B ≅ A) (k : K.obj A ≅ A)
    (hcomp : c.hom.app A ≫ H.map q.hom ≫ r.hom = k.hom)
    (hid : k.hom = i.hom.app A) (n : ℕ) (x : Ext.{eD} V B n) :
    extSectionPullback F H K c i sH A n (x.comp (Ext.mk₀ q.inv) (add_zero n)) =
      H.extCoefficientTransfer sH r.hom n x := by
  have hsection := sectionCoefficient_of_composition c i q r k hcomp hid
  have hsquare : H.map q.inv ≫ (sourceSectionIso c i).hom.app A = r.hom ≫ 𝟙 A := by
    rw [← hsection, ← Category.assoc, ← H.map_comp, q.inv_hom_id, H.map_id,
      Category.id_comp, Category.comp_id]
  have hnat := extCoefficientTransfer_naturality H sH r.hom
    ((sourceSectionIso c i).hom.app A) q.inv (𝟙 A) hsquare n
  have hx := congrArg (fun f => f x) hnat
  change (H.extCoefficientTransfer sH r.hom n x).comp (Ext.mk₀ (𝟙 A)) (add_zero n) =
    H.extCoefficientTransfer sH ((sourceSectionIso c i).hom.app A) n
      (x.comp (Ext.mk₀ q.inv) (add_zero n)) at hx
  rw [Ext.comp_mk₀_id] at hx
  simpa only [extSectionPullback] using hx.symm

end Ext
end CategoryTheory.Functor
