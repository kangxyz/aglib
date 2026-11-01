/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.Iso
public import Aglib.CategoryTheory.NatTrans.TargetComparisonEquation

/-! # Original target equations through inverse and composite specified isomorphisms -/
@[expose] public section
namespace CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] {X Y Z T : C}

/-- Reverse a proved comparison without changing either original map to the target. -/
theorem targetComparison_iso_inv (a : X ≅ Z) (d : Y ≅ Z)
    (bX : X ⟶ T) (bY : Y ⟶ T) (bZ : Z ⟶ T)
    (ha : TargetComparisonEquation a.hom bZ bX)
    (hd : TargetComparisonEquation d.hom bZ bY) :
    TargetComparisonEquation (a ≪≫ d.symm).hom bY bX := by
  change (a.hom ≫ d.inv) ≫ bY = bX
  rw [← hd, Category.assoc, ← Category.assoc d.inv, d.inv_hom_id,
    Category.id_comp]
  exact ha

/-- Compose two proved normalization equations at the shared whole-map boundary. -/
theorem targetComparison_iso_trans (a : X ≅ Y) (d : Y ≅ Z)
    (bX : X ⟶ T) (bY : Y ⟶ T) (bZ : Z ⟶ T)
    (ha : TargetComparisonEquation a.hom bY bX)
    (hd : TargetComparisonEquation d.hom bZ bY) :
    TargetComparisonEquation (a ≪≫ d).hom bZ bX := by
  change (a.hom ≫ d.hom) ≫ bZ = bX
  rw [Category.assoc, hd]
  exact ha
end CategoryTheory
