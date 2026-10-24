/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ExactMateCube
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Reflecting invertibility through the original mate-cube equation

The six transformations remain the supplied original maps. If the four
comparison transformations and the target exchange are invertible, a
conservative comparison functor reflects invertibility of the source exchange.
The finite module-sheaf base-change theorem supplies these hypotheses from
actual comparisons and the existing finite abelian base-change theorem.
-/

@[expose] public section

namespace CategoryTheory

variable {A B C D A' B' C' D' : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* A'] [Category* B'] [Category* C'] [Category* D']
  {R₁ : B ⥤ A} {R₂ : D ⥤ C} {R₁' : B' ⥤ A'} {R₂' : D' ⥤ C'}
  {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}
  {b₁ : R₁ ⋙ QA ⟶ QB ⋙ R₁'} {b₂ : R₂ ⋙ QC ⟶ QD ⋙ R₂'}
  {μ : R₁ ⋙ G ⟶ H ⋙ R₂} {μ' : R₁' ⋙ G' ⟶ H' ⋙ R₂'}
  {γ : QA ⋙ G' ⟶ G ⋙ QC} {δ : QB ⋙ H' ⟶ H ⋙ QD}

/-- The original exchange is invertible if its conservative comparison is
invertible through the proved original mate-cube equation. -/
theorem HorizontalMateCubeEquation.isIso
    (h : HorizontalMateCubeEquation b₁ b₂ μ μ' γ δ)
    [IsIso b₁] [IsIso b₂] [IsIso γ] [IsIso δ] [IsIso μ']
    [QC.ReflectsIsomorphisms] : IsIso μ := by
  apply (NatTrans.isIso_iff_isIso_app μ).mpr
  intro K
  have ht : IsIso (γ.app (R₁.obj K) ≫ QC.map (μ.app K) ≫ b₂.app (H.obj K)) := by
    rw [← h K]
    infer_instance
  have hr : IsIso (QC.map (μ.app K) ≫ b₂.app (H.obj K)) :=
    (isIso_comp_left_iff (γ.app (R₁.obj K)) _).mp ht
  have : IsIso (QC.map (μ.app K)) :=
    (isIso_comp_right_iff _ (b₂.app (H.obj K))).mp hr
  exact isIso_of_reflects_iso (μ.app K) QC

end CategoryTheory
