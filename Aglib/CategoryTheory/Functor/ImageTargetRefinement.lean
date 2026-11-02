/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionAssembly

/-! # The original composition square when only the total derived model changes -/

@[expose] public section
namespace CategoryTheory
variable {A B C₀ C₁ M N Z : Type*}
  [Category* A] [Category* B] [Category* C₀] [Category* C₁]
  [Category* M] [Category* N] [Category* Z]
  {K : A ⥤ B} {Q : B ⥤ M} {I : M ⥤ N} {P : N ⥤ Z}
  {J₀ : A ⥤ C₀} {J₁ : A ⥤ C₁} {S₀ : C₀ ⥤ Z} {S₁ : C₁ ⥤ Z}

/-- The actual total comparison postcomposes the unchanged original source route. -/
def ImageTargetRefinementEquation (τ : J₀ ⋙ S₀ ⟶ J₁ ⋙ S₁)
    (α₀ : K ⋙ Q ⋙ I ⋙ P ⟶ J₀ ⋙ S₀) (α₁ : K ⋙ Q ⋙ I ⋙ P ⟶ J₁ ⋙ S₁) : Prop :=
  α₁ = α₀ ≫ τ

/-- Only proved identity-image faces are removed from the original whole cube. -/
theorem imageTargetRefinementEquation
    (τK : K ⋙ Q ⟶ K ⋙ Q) (τI : I ⋙ P ⟶ I ⋙ P) (τ : J₀ ⋙ S₀ ⟶ J₁ ⋙ S₁)
    (α₀ : K ⋙ Q ⋙ I ⋙ P ⟶ J₀ ⋙ S₀) (α₁ : K ⋙ Q ⋙ I ⋙ P ⟶ J₁ ⋙ S₁)
    (hK : τK = 𝟙 _) (hI : τI = 𝟙 _)
    (h : ImageCompositionNaturalityEquation τK τI τ α₀ α₁) :
    ImageTargetRefinementEquation τ α₀ α₁ := by
  subst τK
  subst τI
  simpa only [ImageCompositionNaturalityEquation, ImageTargetRefinementEquation,
    Functor.whiskerRight_id', Functor.whiskerLeft_id', Category.id_comp] using h

end CategoryTheory
