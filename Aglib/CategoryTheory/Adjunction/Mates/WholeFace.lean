/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.CategoryTheory.Adjunction.Mates.InverseNaturality

/-! # Whole face naturality from the original identified mates -/
@[expose] public section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory
variable {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  {G G' : C ⥤ E} {H H' : D ⥤ F}

/-- A proved face law for the actual identified right mates gives the original
left face law, without any assumed compatibility on the left. -/
theorem mateEquiv_face_of_identified (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (α' : TwoSquare G' L₁ L₂ H')
    (γ : G ⟶ G') (δ : H ⟶ H')
    (ρ : R₁ ⋙ G ⟶ H ⋙ R₂) (ρ' : R₁ ⋙ G' ⟶ H' ⋙ R₂)
    (hα : (mateEquiv a₁ a₂ α).natTrans = ρ)
    (hα' : (mateEquiv a₁ a₂ α').natTrans = ρ')
    (h : whiskerLeft R₁ γ ≫ ρ' = ρ ≫ whiskerRight δ R₂) :
    whiskerRight γ L₂ ≫ α'.natTrans = α.natTrans ≫ whiskerLeft L₁ δ := by
  have hh : ∀ K, γ.app (R₁.obj K) ≫ (mateEquiv a₁ a₂ α').natTrans.app K =
      (mateEquiv a₁ a₂ α).natTrans.app K ≫ R₂.map (δ.app K) := by
    intro K
    rw [hα, hα']
    exact congrArg (fun z => z.app K) h
  apply NatTrans.ext
  funext X
  have hm := mateEquiv_symm_top_bottom_naturality a₁ a₂
    (mateEquiv a₁ a₂ α) (mateEquiv a₁ a₂ α') γ δ hh X
  simpa only [Equiv.symm_apply_apply, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app] using hm

end CategoryTheory
