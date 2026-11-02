/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ImageFirstRefinement
public import Aglib.CategoryTheory.Functor.ImageTargetRefinement

/-! # Combine original first-presentation refinement with independent total-model transport -/

@[expose] public section
namespace CategoryTheory
variable {A B₀ B₁ C₀ C₁ M N Z : Type*}
  [Category* A] [Category* B₀] [Category* B₁] [Category* C₀] [Category* C₁]
  [Category* M] [Category* N] [Category* Z]
  {K₀ : A ⥤ B₀} {K₁ : A ⥤ B₁} {Q₀ : B₀ ⥤ M} {Q₁ : B₁ ⥤ M}
  {I : M ⥤ N} {P : N ⥤ Z}
  {J₀ : A ⥤ C₀} {J₁ : A ⥤ C₁} {S₀ : C₀ ⥤ Z} {S₁ : C₁ ⥤ Z}

/-- Both specified original comparisons are retained in the same complete map square. -/
def ImageFirstTargetEquation (τK : K₀ ⋙ Q₀ ⟶ K₁ ⋙ Q₁)
    (τT : J₀ ⋙ S₀ ⟶ J₁ ⋙ S₁)
    (α₀ : K₀ ⋙ Q₀ ⋙ I ⋙ P ⟶ J₀ ⋙ S₀)
    (α₁ : K₁ ⋙ Q₁ ⋙ I ⋙ P ⟶ J₁ ⋙ S₁) : Prop :=
  Functor.whiskerRight τK (I ⋙ P) ≫ α₁ = α₀ ≫ τT

/-- The two already proved original comparison squares compose without changing a map. -/
theorem imageFirstTargetEquation (τK : K₀ ⋙ Q₀ ⟶ K₁ ⋙ Q₁)
    (τT : J₀ ⋙ S₀ ⟶ J₁ ⋙ S₁)
    (α₀ : K₀ ⋙ Q₀ ⋙ I ⋙ P ⟶ J₀ ⋙ S₀)
    (αmid : K₀ ⋙ Q₀ ⋙ I ⋙ P ⟶ J₁ ⋙ S₁)
    (α₁ : K₁ ⋙ Q₁ ⋙ I ⋙ P ⟶ J₁ ⋙ S₁)
    (hFirst : ImageFirstRefinementEquation τK αmid α₁)
    (hTarget : ImageTargetRefinementEquation τT α₀ αmid) :
    ImageFirstTargetEquation τK τT α₀ α₁ := hFirst.trans hTarget

end CategoryTheory
