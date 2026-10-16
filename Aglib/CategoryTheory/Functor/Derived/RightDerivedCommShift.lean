/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift

/-!
# Shift compatibility of original right-derived descents

A comparison from a right-derived functor commutes with shifts whenever
its original defining unit square does. This uses the uniqueness of the
native right-derived descent, without choosing a new derived functor or
assuming that the comparison is an isomorphism.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC uD vD uH vH uA

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {H : Type uH} [Category.{vH} H] {F : C ⥤ D} {L : C ⥤ H}
    {RF G : H ⥤ D} (α : F ⟶ L ⋙ RF) (W : MorphismProperty C)
    [L.IsLocalization W] [RF.IsRightDerivedFunctor α W]
    (A : Type uA) [AddGroup A] [HasShift C A] [HasShift D A] [HasShift H A]
    [W.IsCompatibleWithShift A] [F.CommShift A] [L.CommShift A]
    [RF.CommShift A] [G.CommShift A] [α.CommShift A]

include W in
/-- The original unit square detects shift compatibility of a right-derived
comparison. No invertibility assumption on the comparison is made. -/
theorem commShift_of_rightDerived_fac (τ : RF ⟶ G) (β : F ⟶ L ⋙ G)
    [β.CommShift A] (h : α ≫ whiskerLeft L τ = β) : τ.CommShift A := by
  constructor
  intro a
  apply rightDerived_ext _ (IsRightDerivedFunctor.precomposeShiftNatTrans RF α a) W
  ext X
  have hfac (Y : C) : α.app Y ≫ τ.app (L.obj Y) = β.app Y := congr_app h Y
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    IsRightDerivedFunctor.precomposeShiftNatTrans_app, Category.assoc]
  have hα := NatTrans.shift_app_comm α a X
  simp only [commShiftIso_comp_hom_app] at hα
  rw [← reassoc_of% hα, ← (shiftFunctor D a).map_comp, hfac]
  have hτ := τ.naturality ((L.commShiftIso a).hom.app X)
  dsimp only [comp_obj] at hτ
  rw [reassoc_of% hτ]
  rw [← Category.assoc, hfac (X⟦a⟧)]
  simpa only [commShiftIso_comp_hom_app, Category.assoc] using NatTrans.shift_app_comm β a X

/-- The native right-derived descent of a shift-compatible original unit square
commutes with shifts. -/
instance rightDerivedDesc_commShift (β : F ⟶ L ⋙ G) [β.CommShift A] :
    (RF.rightDerivedDesc α W G β).CommShift A :=
  commShift_of_rightDerived_fac α W A _ β (RF.rightDerived_fac α W G β)

end CategoryTheory.Functor
