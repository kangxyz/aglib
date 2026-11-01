/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.TripleMateCompatibility

/-! # Retaining a specified structural square in outer-adjoint compatibility -/

@[expose] public noncomputable section
namespace CategoryTheory.Adjunction
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {J : A ⥤ B} {Q : B ⥤ A} {S : A ⥤ B}
  {J' : C ⥤ D} {Q' : D ⥤ C} {S' : C ⥤ D}
  {R : D ⥤ B} {R' : C ⥤ A}
  (t : Triple J Q S) (t' : Triple J' Q' S')
  [J.Full] [J.Faithful] [J'.Full] [J'.Faithful]

/-- The square retains the actual mixed map and the actual structural right comparison. -/
def TripleMateStructuralEquation (σ : R' ⋙ J ⟶ J' ⋙ R) (γ : S' ⋙ R ⟶ R' ⋙ S) : Prop :=
  ∀ K, σ.app K ≫ R.map (t'.leftToRight.app K) ≫ γ.app K =
    t.leftToRight.app (R'.obj K)

/-- The proved right-mate identification substitutes the original structural square. -/
theorem tripleMateStructuralEquation (β : R ⋙ Q ≅ Q' ⋙ R')
    (σ : R' ⋙ J ⟶ J' ⋙ R) (γ : S' ⋙ R ⟶ R' ⋙ S)
    (h : TripleMateCompatibilityEquation t t' β σ)
    (hγ : (mateEquiv t'.adj₂ t.adj₂ (TwoSquare.mk _ _ _ _ β.hom)).natTrans = γ) :
    TripleMateStructuralEquation t t' σ γ := by
  subst γ
  exact h

end CategoryTheory.Adjunction
