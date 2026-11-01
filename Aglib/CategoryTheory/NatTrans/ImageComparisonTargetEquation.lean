/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ToTargetAlgebra
public import Aglib.CategoryTheory.NatTrans.TargetComparisonEquation

/-! # Whole original comparison equations before concrete whiskering -/
@[expose] public noncomputable section
namespace CategoryTheory
variable {U A B T : Type*} [Category* U]
  [Category* A] [Category* B] [Category* T]
  {L₁ S₁ : U ⥤ A} {L₂ S₂ : U ⥤ B} {R₁ : A ⥤ T} {R₂ : B ⥤ T}
  {F : A ⥤ B} {H : U ⥤ T}

/-- Consume the whole original square and restrict only after its generic proof. -/
theorem imageComparison_toTarget_equation
    (δ : L₂ ⟶ L₁ ⋙ F) (b₁ : L₁ ⟶ S₁) (b₂ : L₂ ⟶ S₂)
    (c : S₁ ⋙ F ≅ S₂) (e : F ⋙ R₂ ≅ R₁)
    (t₁ : S₁ ⋙ R₁ ≅ H) (t₂ : S₂ ⋙ R₂ ≅ H)
    (hδ : δ ≫ Functor.whiskerRight b₁ F ≫ c.hom = b₂)
    (ht : Functor.isoWhiskerLeft S₁ e ≪≫ t₁ =
      (Functor.associator S₁ F R₂).symm ≪≫ Functor.isoWhiskerRight c R₂ ≪≫ t₂) :
    TargetComparisonEquation (imageComparison δ e)
      (Functor.whiskerRight b₁ R₁ ≫ t₁.hom)
      (Functor.whiskerRight b₂ R₂ ≫ t₂.hom) :=
  imageComparison_toTarget δ b₁ b₂ c e t₁ t₂
    (fun K => congrArg (fun z => z.app K) hδ) ht
end CategoryTheory
