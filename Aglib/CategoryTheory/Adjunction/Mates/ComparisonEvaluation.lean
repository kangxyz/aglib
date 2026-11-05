/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Adjunction.Mates.Chart

/-! # Evaluate the complete comparison before native specialization -/
@[expose] public section
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory.SourceChartMates
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  {L₀ : C₀ ⥤ D₀} {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂}
  {P : C₀ ⥤ C₁} {Q : D₀ ⥤ D₁}
  {F : C₁ ⥤ C₂} {G : D₁ ⥤ D₂}
  {A : C₀ ⥤ C₂} {B : D₀ ⥤ D₂}

theorem comparison_app (e : P ⋙ L₁ ≅ L₀ ⋙ Q) (α : F ⋙ L₂ ⟶ L₁ ⋙ G)
    (s : A ≅ P ⋙ F) (t : B ≅ Q ⋙ G) (X : C₀) :
    (comparison e α s t).app X =
      (sourceIso s L₂).hom.app X ≫ α.app (P.obj X) ≫ (targetIso e t).hom.app X := rfl

end CategoryTheory.SourceChartMates
