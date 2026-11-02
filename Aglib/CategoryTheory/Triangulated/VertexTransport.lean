/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Transport of all original triangle arrows through specified vertex isomorphisms -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
namespace CategoryTheory.Pretriangulated.Triangle
variable {C : Type*} [Category* C] [HasShift C ℤ]
  (T : Triangle C) {X₁ X₂ X₃ : C}
  (e₁ : T.obj₁ ≅ X₁) (e₂ : T.obj₂ ≅ X₂) (e₃ : T.obj₃ ≅ X₃)

/-- Conjugate each original arrow, including the connecting map. -/
def transportVertices : Triangle C :=
  Triangle.mk (e₁.inv ≫ T.mor₁ ≫ e₂.hom) (e₂.inv ≫ T.mor₂ ≫ e₃.hom)
    (e₃.inv ≫ T.mor₃ ≫ (CategoryTheory.shiftFunctor C (1 : ℤ)).map e₁.hom)

/-- The specified vertex isomorphisms form the actual triangle isomorphism. -/
def transportVerticesIso : T ≅ transportVertices T e₁ e₂ e₃ := by
  refine Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_
  all_goals simp [transportVertices]

variable [CategoryTheory.Limits.HasZeroObject C] [Preadditive C]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
/-- Transport retains distinguishedness of the original triangle. -/
theorem transportVertices_distinguished (h : T ∈ distTriang C) :
    transportVertices T e₁ e₂ e₃ ∈ distTriang C :=
  isomorphic_distinguished _ h _ (transportVerticesIso T e₁ e₂ e₃).symm
end CategoryTheory.Pretriangulated.Triangle
