/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageCompositionAssembly

/-! # The original composition square when only its first presentation changes -/

@[expose] public section
namespace CategoryTheory
variable {A B₀ B₁ C M N Z : Type*}
  [Category* A] [Category* B₀] [Category* B₁] [Category* C]
  [Category* M] [Category* N] [Category* Z]
  {K₀ : A ⥤ B₀} {K₁ : A ⥤ B₁} {J : A ⥤ C}
  {Q₀ : B₀ ⥤ M} {Q₁ : B₁ ⥤ M} {I : M ⥤ N} {P : N ⥤ Z} {S : C ⥤ Z}

/-- The same specified maps, with unchanged target and total image presentations. -/
def ImageFirstRefinementEquation (τK : K₀ ⋙ Q₀ ⟶ K₁ ⋙ Q₁)
    (α₀ : K₀ ⋙ Q₀ ⋙ I ⋙ P ⟶ J ⋙ S) (α₁ : K₁ ⋙ Q₁ ⋙ I ⋙ P ⟶ J ⋙ S) : Prop :=
  Functor.whiskerRight τK (I ⋙ P) ≫ α₁ = α₀

/-- The actual identity-image equations remove the two unchanged faces of the proved cube. -/
theorem imageFirstRefinementEquation (τK : K₀ ⋙ Q₀ ⟶ K₁ ⋙ Q₁)
    (τI : I ⋙ P ⟶ I ⋙ P) (τJ : J ⋙ S ⟶ J ⋙ S)
    (α₀ : K₀ ⋙ Q₀ ⋙ I ⋙ P ⟶ J ⋙ S) (α₁ : K₁ ⋙ Q₁ ⋙ I ⋙ P ⟶ J ⋙ S)
    (hI : τI = 𝟙 _) (hJ : τJ = 𝟙 _)
    (h : ImageCompositionNaturalityEquation τK τI τJ α₀ α₁) :
    ImageFirstRefinementEquation τK α₀ α₁ := by
  subst τI
  subst τJ
  simpa only [ImageCompositionNaturalityEquation, ImageFirstRefinementEquation,
    Functor.whiskerLeft_id', Category.id_comp, Category.comp_id] using h

end CategoryTheory
