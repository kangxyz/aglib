/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageRightUnit

/-! # Retaining the actual refinement map in a supplied right-unit equation -/

@[expose] public section
namespace CategoryTheory
variable {U A B D E : Type*}
  [Category* U] [Category* A] [Category* B] [Category* D] [Category* E]
  {J : U ⥤ A} {L : U ⥤ B} {N : A ⥤ B}
  {Q : A ⥤ E} {P₀ : B ⥤ E} {I : E ⥤ D} {R : D ⥤ E}

/-- A whole identification of the original refinement map transports the supplied equation;
no native component proof is unfolded. -/
theorem rightUnitImageEquation_actualComparison
    (δ : L ⟶ J ⋙ N) (e : N ⋙ P₀ ≅ Q) (ε : I ⋙ R ≅ 𝟭 E)
    (α : J ⋙ Q ⋙ I ⋙ R ⟶ L ⋙ P₀) (β : L ⋙ P₀ ⟶ J ⋙ Q)
    (hβ : β = imageComparison δ e) (h : RightUnitImageEquation δ e ε α) :
    ∀ K, α.app K ≫ β.app K = ε.hom.app (Q.obj (J.obj K)) := by
  subst β
  exact h

/-- The same original comparison gives the whole natural-transformation triangle. -/
theorem rightUnitImageEquation_actualComparison_hom
    (δ : L ⟶ J ⋙ N) (e : N ⋙ P₀ ≅ Q) (ε : I ⋙ R ≅ 𝟭 E)
    (α : J ⋙ Q ⋙ I ⋙ R ⟶ L ⋙ P₀) (β : L ⋙ P₀ ⟶ J ⋙ Q)
    (hβ : β = imageComparison δ e) (h : RightUnitImageEquation δ e ε α) :
    α ≫ β = Functor.whiskerLeft (J ⋙ Q) ε.hom ≫
      (Functor.rightUnitor (J ⋙ Q)).hom := by
  apply NatTrans.ext
  funext K
  change α.app K ≫ β.app K = ε.hom.app (Q.obj (J.obj K)) ≫ 𝟙 _
  rw [Category.comp_id]
  exact rightUnitImageEquation_actualComparison δ e ε α β hβ h K

end CategoryTheory
