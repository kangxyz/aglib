/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Presheaf.SheafificationRestriction

/-!
# Unit equations for the original slice-sheafification comparison

The existing `sheafificationOverIso` is the adjunct of the restricted original
unit. These are its whole unit equations, before evaluating at a coefficient,
slice object or section. No new sheafification or comparison is selected.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite

namespace PresheafOfModules.Restriction

universe u v

private theorem comp_map_inv_of_comp_map_hom
    {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
    {A B : D} {T : E} (e : A ≅ B) (a : T ⟶ F.obj A) (b : T ⟶ F.obj B)
    (h : a ≫ F.map e.hom = b) : b ≫ F.map e.inv = a := by
  rw [← h, Category.assoc, ← CategoryTheory.Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (U : C) [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original comparison sends the slice sheafification unit to the
restriction of the original sheafification unit. -/
theorem sheafificationOverIso_hom_unit (P : _root_.PresheafOfModules.{u} R.obj) :
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 (R.over U).obj)).unit.app
        ((restrictPresheaf R U).obj P) ≫
      (SheafOfModules.forget (R.over U)).map (sheafificationOverIso R U P).hom =
        restrictedSheafificationUnit R U P := by
  apply (_root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 (R.over U).obj)).unit_comp_map_eq_iff _ _ |>.mpr
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse original comparison sends the restricted original unit to
the original unit of sheafification on the slice. -/
theorem sheafificationOverIso_inv_unit (P : _root_.PresheafOfModules.{u} R.obj) :
    restrictedSheafificationUnit R U P ≫
      (SheafOfModules.forget (R.over U)).map (sheafificationOverIso R U P).inv =
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 (R.over U).obj)).unit.app
      ((restrictPresheaf R U).obj P) := by
  exact comp_map_inv_of_comp_map_hom (SheafOfModules.forget (R.over U))
    (sheafificationOverIso R U P) _ _ (sheafificationOverIso_hom_unit R U P)

end PresheafOfModules.Restriction
