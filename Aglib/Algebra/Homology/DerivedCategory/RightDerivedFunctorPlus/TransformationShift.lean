/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Shift compatibility from the original derived-unit equation

A transformation out of a right derived functor commutes with shifts whenever
its factorization through the original derived unit does. The target functor
need not itself be right derived. This applies to the installed restriction
and composition comparisons without choosing another derived functor.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

variable {C H D : Type*} [Category* C] [Category* H] [Category* D]
  [HasShift C ℤ] [HasShift H ℤ] [HasShift D ℤ]
  (L : C ⥤ H) [L.CommShift ℤ] (W : MorphismProperty C)
  [L.IsLocalization W] [W.IsCompatibleWithShift ℤ]
  {F : C ⥤ D} [F.CommShift ℤ] {RF RG : H ⥤ D}
  [RF.CommShift ℤ] [RG.CommShift ℤ]
  (α : F ⟶ L ⋙ RF) (β : F ⟶ L ⋙ RG)
  [RF.IsRightDerivedFunctor α W] [α.CommShift ℤ] [β.CommShift ℤ]

include W

/-- The original derived-unit factorization determines shift compatibility. -/
theorem commShift_of_rightDerived_factorization (δ : RF ⟶ RG)
    (hδ : α ≫ whiskerLeft L δ = β) : δ.CommShift ℤ where
  shift_comm k := by
    apply rightDerived_ext (shiftFunctor H k ⋙ RF)
      (IsRightDerivedFunctor.precomposeShiftNatTrans RF α k) W
    ext X
    have hα := NatTrans.shift_app_comm α k X
    have hβ := NatTrans.shift_app_comm β k X
    have h₀ := congr_app hδ X
    have h₁ := congr_app hδ (X⟦k⟧)
    have hn := δ.naturality ((L.commShiftIso k).hom.app X)
    simp only [commShiftIso_comp_hom_app] at hα hβ
    dsimp only [NatTrans.comp_app, whiskerLeft_app] at h₀ h₁
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      IsRightDerivedFunctor.precomposeShiftNatTrans, associator_hom_app,
      associator_inv_app, Category.comp_id, Category.id_comp]
    calc
      (α.app (X⟦k⟧) ≫ RF.map ((L.commShiftIso k).hom.app X)) ≫
          (RF.commShiftIso k).hom.app (L.obj X) ≫ (δ.app (L.obj X))⟦k⟧' =
          (F.commShiftIso k).hom.app X ≫ (α.app X)⟦k⟧' ≫
            (δ.app (L.obj X))⟦k⟧' := by
        simpa only [Category.assoc] using
          congrArg (fun z => z ≫ (δ.app (L.obj X))⟦k⟧') hα.symm
      _ = (F.commShiftIso k).hom.app X ≫ (β.app X)⟦k⟧' := by
        rw [← (shiftFunctor D k).map_comp, h₀]
      _ = α.app (X⟦k⟧) ≫ δ.app (L.obj (X⟦k⟧)) ≫
          RG.map ((L.commShiftIso k).hom.app X) ≫
            (RG.commShiftIso k).hom.app (L.obj X) := by
        rw [hβ, ← h₁]
        simp only [Category.assoc]
      _ = (α.app (X⟦k⟧) ≫ RF.map ((L.commShiftIso k).hom.app X)) ≫
          δ.app ((L.obj X)⟦k⟧) ≫ (RG.commShiftIso k).hom.app (L.obj X) := by
        simpa only [Category.assoc, Functor.comp_obj] using congrArg
          (fun z => α.app (X⟦k⟧) ≫ z ≫ (RG.commShiftIso k).hom.app (L.obj X)) hn.symm

end CategoryTheory.Functor
