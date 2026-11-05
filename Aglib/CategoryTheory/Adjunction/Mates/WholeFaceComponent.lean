/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Adjunction.Mates.WholeFace

/-! # Explicit original component face before native specialization -/
@[expose] public section
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory
variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  {G G' : C ⥤ E} {H H' : D ⥤ F}

theorem mateEquiv_natTrans_face_component (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (α' : G' ⋙ L₂ ⟶ L₁ ⋙ H')
    (γ : G ⟶ G') (δ : H ⟶ H')
    (ρ : R₁ ⋙ G ⟶ H ⋙ R₂) (ρ' : R₁ ⋙ G' ⟶ H' ⋙ R₂)
    (hα : (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ α)).natTrans = ρ)
    (hα' : (mateEquiv a₁ a₂ (TwoSquare.mk _ _ _ _ α')).natTrans = ρ')
    (h : whiskerLeft R₁ γ ≫ ρ' = ρ ≫ whiskerRight δ R₂) (X : C) :
    L₂.map (γ.app X) ≫ α'.app X = α.app X ≫ δ.app (L₁.obj X) := by
  have hh := congrArg (fun z => z.app X) (mateEquiv_face_of_identified a₁ a₂
    (TwoSquare.mk _ _ _ _ α) (TwoSquare.mk _ _ _ _ α') γ δ ρ ρ' hα hα' h)
  exact hh

end CategoryTheory
