/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.NatIso

/-! # Whole exchange compatibility with original structural-image comparisons -/

@[expose] public section

universe uC vC uD vD uS vS uC' vC' uD' vD' uT vT

namespace CategoryTheory

variable {C : Type uC} {D : Type uD} {S : Type uS} {C' : Type uC'} {D' : Type uD'} {T : Type uT}
  [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
  [Category.{vC'} C'] [Category.{vD'} D'] [Category.{vT} T]
  {R : C ⥤ D} {P₁ : C ⥤ S} {P₂ : D ⥤ S}
  {F : S ⥤ T} {Q₁ : C ⥤ C'} {Q₂ : D ⥤ D'}
  {R' : C' ⥤ D'} {P₁' : C' ⥤ T} {P₂' : D' ⥤ T}

/-- Original exchange pasting in the actual structural-image normalization. -/
def OverComparisonBaseChangeEquation
    (τ : R ⋙ P₂ ≅ P₁) (τ' : R' ⋙ P₂' ≅ P₁')
    (β₁ : P₁ ⋙ F ⟶ Q₁ ⋙ P₁') (β₂ : P₂ ⋙ F ⟶ Q₂ ⋙ P₂')
    (βR : R ⋙ Q₂ ⟶ Q₁ ⋙ R') : Prop :=
  ∀ M, F.map (τ.hom.app M) ≫ β₁.app M ≫ τ'.inv.app (Q₁.obj M) =
    β₂.app (R.obj M) ≫ P₂'.map (βR.app M)

/-- Normalize the original vertical pasting by its two specified compositors.
The exchange maps are unchanged; no invertibility of an exchange is assumed. -/
theorem overComparisonBaseChangeEquation_of_vertical_pasting
    (c : P₁ ≅ R ⋙ P₂) (c' : P₁' ≅ R' ⋙ P₂')
    (β₁ : P₁ ⋙ F ⟶ Q₁ ⋙ P₁') (β₂ : P₂ ⋙ F ⟶ Q₂ ⋙ P₂')
    (βR : R ⋙ Q₂ ⟶ Q₁ ⋙ R')
    (h : ∀ M, F.map (c.hom.app M) ≫ β₂.app (R.obj M) ≫ P₂'.map (βR.app M) =
      β₁.app M ≫ c'.hom.app (Q₁.obj M)) :
    OverComparisonBaseChangeEquation c.symm c'.symm β₁ β₂ βR := by
  intro M
  change F.map (c.inv.app M) ≫ β₁.app M ≫ c'.hom.app (Q₁.obj M) = _
  apply (cancel_epi (F.map (c.hom.app M))).mp
  rw [← F.map_comp_assoc, c.hom_inv_id_app, F.map_id, Category.id_comp]
  exact (h M).symm

end CategoryTheory
