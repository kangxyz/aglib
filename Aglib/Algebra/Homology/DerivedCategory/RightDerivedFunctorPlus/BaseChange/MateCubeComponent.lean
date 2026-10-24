/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ExactMateCube

/-!
# Components of the original horizontal mate-cube equation

The literal component equation is evaluated with arbitrary functors and whole
transformations. Concrete consumers can use this opaque evaluator without
unfolding the mate-cube proposition at their native comparison maps.
-/

@[expose] public section

namespace CategoryTheory

variable {A B C D A' B' C' D' : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D]
  [Category* A'] [Category* B'] [Category* C'] [Category* D']
  {R₁ : B ⥤ A} {R₂ : D ⥤ C} {R₁' : B' ⥤ A'} {R₂' : D' ⥤ C'}
  {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}

/-- Evaluate the proved literal cube equation at one object, keeping all six
comparison transformations as parameters. -/
theorem horizontalMateCubeEquation_app
    (b₁ : R₁ ⋙ QA ⟶ QB ⋙ R₁') (b₂ : R₂ ⋙ QC ⟶ QD ⋙ R₂')
    (μ : R₁ ⋙ G ⟶ H ⋙ R₂) (μ' : R₁' ⋙ G' ⟶ H' ⋙ R₂')
    (γ : QA ⋙ G' ⟶ G ⋙ QC) (δ : QB ⋙ H' ⟶ H ⋙ QD)
    (h : HorizontalMateCubeEquation b₁ b₂ μ μ' γ δ) (K : B) :
    G'.map (b₁.app K) ≫ μ'.app (QB.obj K) ≫ R₂'.map (δ.app K) =
      γ.app (R₁.obj K) ≫ QC.map (μ.app K) ≫ b₂.app (H.obj K) :=
  h K

end CategoryTheory
