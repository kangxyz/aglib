/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ExactMateCube
public import Aglib.CategoryTheory.Adjunction.Mates.UnitIsomorphism

/-! # Invertibility reflected to the restricted source of an original mate cube -/

@[expose] public section

namespace CategoryTheory

universe uA vA uB vB uC vC uD vD uA' vA' uB' vB' uC' vC' uD' vD'

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {A' : Type uA'} [Category.{vA'} A'] {B' : Type uB'} [Category.{vB'} B']
  {C' : Type uC'} [Category.{vC'} C'] {D' : Type uD'} [Category.{vD'} D']
  {R₁ : B ⥤ A} {R₂ : D ⥤ C} {R₁' : B' ⥤ A'} {R₂' : D' ⥤ C'}
  {G : A ⥤ C} {H : B ⥤ D} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
  {QA : A ⥤ A'} {QB : B ⥤ B'} {QC : C ⥤ C'} {QD : D ⥤ D'}
  {b₁ : R₁ ⋙ QA ⟶ QB ⋙ R₁'} {b₂ : R₂ ⋙ QC ⟶ QD ⋙ R₂'}
  {μ : R₁ ⋙ G ⟶ H ⋙ R₂} {μ' : R₁' ⋙ G' ⟶ H' ⋙ R₂'}
  {γ : QA ⋙ G' ⟶ G ⋙ QC} {δ : QB ⋙ H' ⟶ H ⋙ QD}

/-- Invertibility of the target exchange and the four original comparison
components implies invertibility of the restricted source exchange component. -/
theorem HorizontalMateCubeEquation.isIso_source_map_app
    (h : HorizontalMateCubeEquation b₁ b₂ μ μ' γ δ) (K : B)
    [IsIso (b₁.app K)] [IsIso (b₂.app (H.obj K))]
    [IsIso (γ.app (R₁.obj K))] [IsIso (δ.app K)] [IsIso (μ'.app (QB.obj K))] :
    IsIso (QC.map (μ.app K)) := by
  exact isIso_of_component_equation (𝟭 C') (QC.map (μ.app K))
    (G'.map (b₁.app K)) (R₂'.map (δ.app K))
    (γ.app (R₁.obj K)) (b₂.app (H.obj K)) (h K)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance

end CategoryTheory
