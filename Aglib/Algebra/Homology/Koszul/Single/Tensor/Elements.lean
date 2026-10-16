/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Aglib.Algebra.Homology.Koszul.Single.Tensor.Differential

/-!
# Elementwise two-column identities

These identities expose the checked categorical splitting and differential as
module-element formulas, for the cycle and boundary calculations used in the
scalar-quotient comparison.
-/

@[expose] public section

universe u

open CategoryTheory

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R] (a : R) (K : ChainComplex (ModuleCat.{u} R) ℕ)

@[simp]
theorem singleTensorπZero_ιZero_apply (n : ℕ) (x : K.X n) :
    singleTensorπZero a K n (singleTensorιZero a K n x) = x :=
  ConcreteCategory.congr_hom (singleTensorιZero_πZero a K n) x

@[simp]
theorem singleTensorπOne_ιOne_apply (n : ℕ) (x : K.X n) :
    singleTensorπOne a K n (singleTensorιOne a K n x) = x :=
  ConcreteCategory.congr_hom (singleTensorιOne_πOne a K n) x

@[simp]
theorem singleTensorπOne_ιZero_apply (n : ℕ) (x : K.X (n + 1)) :
    singleTensorπOne a K n (singleTensorιZero a K (n + 1) x) = 0 :=
  ConcreteCategory.congr_hom (singleTensorιZero_πOne a K n) x

@[simp]
theorem singleTensorπZero_ιOne_apply (n : ℕ) (x : K.X n) :
    singleTensorπZero a K (n + 1) (singleTensorιOne a K n x) = 0 :=
  ConcreteCategory.congr_hom (singleTensorιOne_πZero a K n) x

/-- Every positive-degree element is the sum of its two column components. -/
theorem singleTensor_decomposition_apply (n : ℕ)
    (x : (HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 1)) :
    singleTensorιZero a K (n + 1) (singleTensorπZero a K (n + 1) x) +
      singleTensorιOne a K n (singleTensorπOne a K n x) = x :=
  ConcreteCategory.congr_hom (singleTensor_decomposition a K n) x

/-- Every degree-zero element is its old-column component. -/
theorem singleTensor_decomposition_zero_apply
    (x : (HomologicalComplex.tensorObj (singleComplex R a) K).X 0) :
    singleTensorιZero a K 0 (singleTensorπZero a K 0 x) = x :=
  ConcreteCategory.congr_hom (singleTensor_decomposition_zero a K) x

/-- Equality is detected by the two column projections. -/
theorem singleTensor_ext (n : ℕ)
    {x y : (HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 1)}
    (h₀ : singleTensorπZero a K (n + 1) x = singleTensorπZero a K (n + 1) y)
    (h₁ : singleTensorπOne a K n x = singleTensorπOne a K n y) : x = y := by
  rw [← singleTensor_decomposition_apply a K n x,
    ← singleTensor_decomposition_apply a K n y, h₀, h₁]

/-- Equality in degree zero is detected by the old-column projection. -/
theorem singleTensor_ext_zero
    {x y : (HomologicalComplex.tensorObj (singleComplex R a) K).X 0}
    (h : singleTensorπZero a K 0 x = singleTensorπZero a K 0 y) : x = y := by
  rw [← singleTensor_decomposition_zero_apply a K x,
    ← singleTensor_decomposition_zero_apply a K y, h]

@[simp]
theorem singleTensor_d_ιZero_apply (n : ℕ) (x : K.X (n + 1)) :
    (HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 1) n
        (singleTensorιZero a K (n + 1) x) =
      singleTensorιZero a K n (K.d (n + 1) n x) :=
  ConcreteCategory.congr_hom (singleTensorιZero_d a K n) x

@[simp]
theorem singleTensor_d_ιOne_apply (n : ℕ) (x : K.X (n + 1)) :
    (HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 2) (n + 1)
        (singleTensorιOne a K (n + 1) x) =
      singleTensorιZero a K (n + 1) (a • x) -
        singleTensorιOne a K n (K.d (n + 1) n x) :=
  ConcreteCategory.congr_hom (singleTensorιOne_d a K n) x

@[simp]
theorem singleTensor_d_ιOne_zero_apply (x : K.X 0) :
    (HomologicalComplex.tensorObj (singleComplex R a) K).d 1 0
        (singleTensorιOne a K 0 x) = singleTensorιZero a K 0 (a • x) :=
  ConcreteCategory.congr_hom (singleTensorιOne_zero_d a K) x

@[simp]
theorem singleTensorπZero_d_apply (n : ℕ)
    (x : (HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 1)) :
    singleTensorπZero a K n
        ((HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 1) n x) =
      K.d (n + 1) n (singleTensorπZero a K (n + 1) x) + a • singleTensorπOne a K n x :=
  ConcreteCategory.congr_hom (singleTensor_d_πZero a K n) x

@[simp]
theorem singleTensorπOne_d_apply (n : ℕ)
    (x : (HomologicalComplex.tensorObj (singleComplex R a) K).X (n + 2)) :
    singleTensorπOne a K n
        ((HomologicalComplex.tensorObj (singleComplex R a) K).d (n + 2) (n + 1) x) =
      -(K.d (n + 1) n (singleTensorπOne a K (n + 1) x)) :=
  ConcreteCategory.congr_hom (singleTensor_d_πOne a K n) x

end ChainComplex.Koszul
