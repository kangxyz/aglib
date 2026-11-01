/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.OpenCompositionCoherence

/-! # Retain the original backwards total comparison before inverting it -/

@[expose] public section
namespace CategoryTheory
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {F : A ⥤ B} {G : B ⥤ C} {H : C ⥤ D}
  {M : A ⥤ C} {N : B ⥤ D} {P P' : A ⥤ D}

/-- The literal total comparison is retained in its original refinement direction. -/
def OpenCompositionPostEquation (c₀₁ : F ⋙ G ≅ M) (c₁₂ : M ⋙ H ≅ P)
    (c₀₂ : F ⋙ N ≅ P') (cMN : G ⋙ H ≅ N) (e : P' ≅ P) : Prop :=
  Functor.isoWhiskerRight c₀₁ H ≪≫ c₁₂ =
    Functor.associator F G H ≪≫ Functor.isoWhiskerLeft F cMN ≪≫ c₀₂ ≪≫ e

/-- Invert the same original total comparison, only after proving the full map equation. -/
theorem openCompositionEquation_of_post
    (c₀₁ : F ⋙ G ≅ M) (c₁₂ : M ⋙ H ≅ P)
    (c₀₂ : F ⋙ N ≅ P') (cMN : G ⋙ H ≅ N) (e : P' ≅ P)
    (h : OpenCompositionPostEquation c₀₁ c₁₂ c₀₂ cMN e) :
    OpenCompositionEquation c₀₁ (c₁₂ ≪≫ e.symm) c₀₂ cMN := by
  have hp := congrArg (fun z => z ≪≫ e.symm) h
  simpa only [OpenCompositionEquation, Iso.trans_assoc, Iso.self_symm_id,
    Iso.trans_refl] using hp

end CategoryTheory
