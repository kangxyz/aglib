/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.SepClosedConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GlobalSectionsField

/-! # Actual constant higher images over separably closed fields

The constant coefficient is the original higher-image section group, already
in the native value universe. Its comparison with original cohomology is the
proved original map, not a new cohomology object or an arbitrary equivalence.
The actual constant-adjunction counit fixes the normalization on all classes.
No proper base-change theorem is assumed or proved here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω]

/-- Original sections of the actual constant identification are precisely the
original constant-adjunction unit, by its triangle identity. -/
theorem globalSections_fieldTorsionConstantIso_hom
    (G : AbelianSheaf.{u, u + 1} (Spec (.of Ω)))
    (hG : IsAddTorsion ((globalSections (Spec (.of Ω))).obj G)) :
    (globalSections (Spec (.of Ω))).map (fieldTorsionConstantIso Ω G hG).hom =
      (constantAdjunction (Spec (.of Ω))).unit.app
        ((globalSections (Spec (.of Ω))).obj G) := by
  let a := constantAdjunction (Spec (.of Ω))
  let e := fieldTorsionConstantIso Ω G hG
  let : IsIso (a.counit.app G) := constantCounit_isIso_of_field_torsionSections Ω G hG
  change (globalSections (Spec (.of Ω))).map e.hom = a.unit.app _
  apply (cancel_mono ((globalSections (Spec (.of Ω))).map (a.counit.app G))).mp
  rw [← CategoryTheory.Functor.map_comp]
  have he : e.hom ≫ a.counit.app G = 𝟙 G := e.hom_inv_id
  rw [he, CategoryTheory.Functor.map_id]
  exact (a.right_triangle_components G).symm

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of Ω))
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
  (hA : IsAddTorsion ((globalSections (Spec (.of Ω))).obj ((higherDirectImage f q).obj F)))

/-- The original higher image is actually constant with its original section
group. That group's comparison with original H is the same bijective map. -/
def higherDirectImageFieldConstantIso :
    (higherDirectImage f q).obj F ≅
      (constantSheaf (Spec (.of Ω)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((globalSections (Spec (.of Ω))).obj ((higherDirectImage f q).obj F)) :=
  fieldTorsionConstantIso Ω ((higherDirectImage f q).obj F) hA

/-- Under the actual constant identification, every original cohomology class
is the original constant section of its original cohomology-to-sections value.
Independent original Ext universes are not replaced by value-size assumptions. -/
theorem higherDirectImageFieldConstantIso_original_class (x : Sheaf.H.{w} F q) :
    (globalSections (Spec (.of Ω))).map
        (higherDirectImageFieldConstantIso Ω f F q hA).hom
          (cohomologyToHigherSections f F q x) =
      (constantAdjunction (Spec (.of Ω))).unit.app
        ((globalSections (Spec (.of Ω))).obj ((higherDirectImage f q).obj F))
          (cohomologyToHigherSections f F q x) :=
  ConcreteCategory.congr_hom
    (globalSections_fieldTorsionConstantIso_hom Ω ((higherDirectImage f q).obj F) hA) _

end AlgebraicGeometry.Scheme.EtaleCohomology
