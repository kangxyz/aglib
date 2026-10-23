/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Amitsur.Opposite
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Augment

/-!
# The native augmented alternating coface complex

This applies the native `CochainComplex.augment` construction to the native
alternating coface complex and the original cosimplicial augmentation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open scoped Simplicial

namespace AlgebraicTopology.Amitsur

universe v u

variable {C : Type u} [Category.{v} C]

/-- Both original degree-zero cofaces have the same original augmentation composite. -/
theorem augmentation_comp_coface (X : CosimplicialObject.Augmented C) (i : Fin 2) :
    X.hom.app ⦋0⦌ ≫ X.right.δ i = X.hom.app ⦋1⦌ := by
  have h := X.hom.naturality (SimplexCategory.δ i)
  change (𝟙 X.left) ≫ X.hom.app ⦋1⦌ = X.hom.app ⦋0⦌ ≫ X.right.δ i at h
  simpa only [Category.id_comp] using h.symm

variable [Preadditive C]

/-- The original augmentation composes to zero with the original alternating differential. -/
theorem augmentation_comp_d_zero (X : CosimplicialObject.Augmented C) :
    X.hom.app ⦋0⦌ ≫ (AlternatingCofaceMapComplex.obj X.right).d 0 1 = 0 := by
  have hz : X.hom.app ⦋0⦌ ≫ AlternatingCofaceMapComplex.objD X.right 0 = 0 := by
    simp [AlternatingCofaceMapComplex.objD, Fin.sum_univ_two, Preadditive.comp_add,
      augmentation_comp_coface]
  simp only [AlternatingCofaceMapComplex.obj]
  unfold CochainComplex.of.d
  split_ifs
  · rw [← Category.assoc, hz, Limits.zero_comp]
  · rw [Limits.comp_zero]

/-- The actual native augmented cochain complex with its original augmentation in degree zero. -/
def augmentedObj (X : CosimplicialObject.Augmented C) : CochainComplex C ℕ :=
  (AlternatingCofaceMapComplex.obj X.right).augment (X.hom.app ⦋0⦌)
    (augmentation_comp_d_zero X)

@[simp]
theorem augmentedObj_X_zero (X : CosimplicialObject.Augmented C) :
    (augmentedObj X).X 0 = X.left := rfl

@[simp]
theorem augmentedObj_X_succ (X : CosimplicialObject.Augmented C) (n : ℕ) :
    (augmentedObj X).X (n + 1) = X.right.obj ⦋n⦌ := rfl

@[simp]
theorem augmentedObj_d_zero_one (X : CosimplicialObject.Augmented C) :
    (augmentedObj X).d 0 1 = X.hom.app ⦋0⦌ := rfl

/-- Every later original differential is the native alternating sum of original cofaces. -/
theorem augmentedObj_d_succ (X : CosimplicialObject.Augmented C) (n : ℕ) :
    (augmentedObj X).d (n + 1) (n + 2) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.right.δ i := by
  change ((AlternatingCofaceMapComplex.obj X.right).augment _
    (augmentation_comp_d_zero X)).d (n + 1) (n + 2) = _
  rw [CochainComplex.augment_d_succ_succ]
  simpa only [AlternatingCofaceMapComplex.obj, CochainComplex.augment_X_succ,
    Nat.add_assoc, Nat.reduceAdd, AlternatingCofaceMapComplex.objD] using
    CochainComplex.of_d (fun n : ℕ => X.right.obj ⦋n⦌)
      (AlternatingCofaceMapComplex.objD X.right) n

end AlgebraicTopology.Amitsur
