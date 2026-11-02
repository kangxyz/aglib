/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.MateHomEquiv

/-! # Original mixed mates and restriction

Four actual adjunctions and their conjugacy identify the transpose of a mixed
mate. If the open-extension unit is invertible, its transpose is inverse to
the original restriction comparison. No geometrical or exactness hypothesis
is needed for this adjunction calculation.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Adjunction

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  {J : A ⥤ B} {Q : B ⥤ A} {J' : C ⥤ D} {Q' : D ⥤ C}
  {P : B ⥤ D} {R : D ⥤ B} {P' : A ⥤ C} {R' : C ⥤ A}
  (aJ : J ⊣ Q) (aJ' : J' ⊣ Q') (aP : P ⊣ R) (aP' : P' ⊣ R')
  (α : J ⋙ P ⟶ P' ⋙ J') (β : R ⋙ Q ≅ Q' ⋙ R')
  (h : conjugateEquiv (aP'.comp aJ') (aJ.comp aP) α = β.inv)

include h

/-- Transposing the original mixed mate gives the inverse right exchange after
the original open unit. This statement does not assume that unit invertible. -/
theorem mixedMate_homEquiv (K : C) :
    aJ.homEquiv _ _
      (aP.unit.app (J.obj (R'.obj K)) ≫
        R.map (α.app (R'.obj K)) ≫ R.map (J'.map (aP'.counit.app K))) =
      R'.map (aJ'.unit.app K) ≫ β.inv.app (J'.obj K) := by
  have hc : (aP'.comp aJ').homEquiv _ _ (J'.map (aP'.counit.app K)) =
      R'.map (aJ'.unit.app K) := by
    rw [comp_homEquiv]
    change aP'.homEquiv _ _ (aJ'.homEquiv _ _ (J'.map (aP'.counit.app K))) = _
    have hj : aJ'.homEquiv (P'.obj (R'.obj K)) (J'.obj K)
        (J'.map (aP'.counit.app K)) =
        aP'.counit.app K ≫ aJ'.unit.app K := by
      simpa only [Functor.comp_obj, Functor.id_obj, Category.comp_id, homEquiv_id] using
        aJ'.homEquiv_naturality_left (aP'.counit.app K) (𝟙 (J'.obj K))
    dsimp only [Functor.comp_obj, Functor.id_obj] at hj ⊢
    rw [hj, aP'.homEquiv_naturality_right]
    have hp : aP'.homEquiv (R'.obj K) K (aP'.counit.app K) = 𝟙 (R'.obj K) := by
      rw [← aP'.homEquiv_symm_id, Equiv.apply_symm_apply]
    rw [hp, Category.id_comp]
  calc
    _ = (aJ.comp aP).homEquiv _ _
        (α.app (R'.obj K) ≫ J'.map (aP'.counit.app K)) := by
      simp only [comp_homEquiv, Equiv.trans_apply, homEquiv_apply,
        Functor.map_comp]
    _ = (aP'.comp aJ').homEquiv _ _ (J'.map (aP'.counit.app K)) ≫
        (conjugateEquiv (aP'.comp aJ') (aJ.comp aP) α).app (J'.obj K) :=
      homEquiv_conjugate _ _ _ _
    _ = _ := by rw [hc, h]

/-- When the actual open unit is invertible, the transposed mixed mate is a
right inverse to the original exchange restricted along that unit. -/
theorem mixedMate_homEquiv_restriction (K : C) [IsIso (aJ'.unit.app K)] :
    aJ.homEquiv _ _
      (aP.unit.app (J.obj (R'.obj K)) ≫
        R.map (α.app (R'.obj K)) ≫ R.map (J'.map (aP'.counit.app K))) ≫
      (β.hom.app (J'.obj K) ≫ R'.map (inv (aJ'.unit.app K))) =
      𝟙 (R'.obj K) := by
  rw [mixedMate_homEquiv aJ aJ' aP aP' α β h]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← R'.map_comp, IsIso.hom_inv_id, R'.map_id]
  rfl

end CategoryTheory.Adjunction
