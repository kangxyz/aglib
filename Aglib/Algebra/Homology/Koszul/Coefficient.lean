/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Aglib.Algebra.Homology.Koszul.Single.Tensor.Coordinates

/-!
# Finite Koszul complexes with module coefficients

A coefficient module replaces the empty-list tensor unit by the module in
degree zero. Recursion still uses the actual one-element tensor complex.
Regular scalar multiplication on the coefficient module remains regular on
every term, by the proved two-column splitting.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]

/-- The actual finite tensor Koszul complex with a specified coefficient module. -/
noncomputable def coefficientComplex (M : ModuleCat R) : List R → ChainComplex (ModuleCat R) ℕ
  | [] => (ChainComplex.single₀ (ModuleCat R)).obj M
  | a :: s => HomologicalComplex.tensorObj (singleComplex R a) (coefficientComplex M s)

@[simp]
theorem coefficientComplex_nil (M : ModuleCat R) :
    coefficientComplex M [] = (ChainComplex.single₀ (ModuleCat R)).obj M := rfl

@[simp]
theorem coefficientComplex_cons (M : ModuleCat R) (a : R) (s : List R) :
    coefficientComplex M (a :: s) =
      HomologicalComplex.tensorObj (singleComplex R a) (coefficientComplex M s) := rfl

/-- Ring coefficients recover the previously constructed finite Koszul complex. -/
theorem coefficientComplex_ring (s : List R) :
    coefficientComplex (ModuleCat.of R R) s = chainComplex s := by
  induction s with
  | nil => rfl
  | cons a s ih => simp only [coefficientComplex_cons, chainComplex_cons, ih]

/-- Scalar regularity propagates through an actual one-element tensor complex. -/
theorem singleTensor_isSMulRegular (a b : R) (K : ChainComplex (ModuleCat R) ℕ)
    (ha : ∀ n, IsSMulRegular (K.X n) a) (n : ℕ) :
    IsSMulRegular ((HomologicalComplex.tensorObj (singleComplex R b) K).X n) a := by
  intro x y hxy
  have hzero : singleTensorπZero b K n x = singleTensorπZero b K n y :=
    ha n (by simpa only [map_smul] using congrArg (singleTensorπZero b K n).hom hxy)
  cases n with
  | zero =>
    have hx := ConcreteCategory.congr_hom (singleTensor_decomposition_zero b K) x
    have hy := ConcreteCategory.congr_hom (singleTensor_decomposition_zero b K) y
    change singleTensorιZero b K 0 (singleTensorπZero b K 0 x) = x at hx
    change singleTensorιZero b K 0 (singleTensorπZero b K 0 y) = y at hy
    rw [← hx, ← hy, hzero]
  | succ n =>
    have hone : singleTensorπOne b K n x = singleTensorπOne b K n y :=
      ha n (by simpa only [map_smul] using congrArg (singleTensorπOne b K n).hom hxy)
    have hx := ConcreteCategory.congr_hom (singleTensor_decomposition b K n) x
    have hy := ConcreteCategory.congr_hom (singleTensor_decomposition b K n) y
    change singleTensorιZero b K (n + 1) (singleTensorπZero b K (n + 1) x) +
      singleTensorιOne b K n (singleTensorπOne b K n x) = x at hx
    change singleTensorιZero b K (n + 1) (singleTensorπZero b K (n + 1) y) +
      singleTensorιOne b K n (singleTensorπOne b K n y) = y at hy
    rw [← hx, ← hy, hzero, hone]

/-- Regularity on the coefficient module implies regularity on every finite Koszul term. -/
theorem coefficientComplex_isSMulRegular (M : ModuleCat R) (s : List R) (a : R)
    (ha : IsSMulRegular M a) (n : ℕ) : IsSMulRegular ((coefficientComplex M s).X n) a := by
  induction s generalizing n with
  | nil =>
    cases n with
    | zero => exact ha
    | succ n =>
      have : Subsingleton ((coefficientComplex M []).X (n + 1)) :=
        ModuleCat.subsingleton_of_isZero
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 M (n + 1) (by omega))
      exact fun _ _ _ => Subsingleton.elim _ _
  | cons b s ih => exact singleTensor_isSMulRegular a b (coefficientComplex M s) ih n

end ChainComplex.Koszul
