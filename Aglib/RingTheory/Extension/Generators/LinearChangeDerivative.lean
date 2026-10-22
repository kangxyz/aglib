/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Extension.Generators.LinearChange
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Tactic.Ring

/-! # Jacobian entries under the same inverse linear coordinate substitution

The coefficient in the entry formula is exactly the native inverse matrix used
to construct the new generators, not an independently chosen matrix.
-/

@[expose] public noncomputable section

open MvPolynomial
open scoped Matrix

namespace Algebra.Generators

variable {R B n : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [Fintype n] [DecidableEq n]
variable (U : Matrix n n R)

/-- The derivative of an inverse-substituted coordinate is its actual inverse-matrix entry. -/
theorem pderiv_inverseLinearSubstitution_X (i j : n) :
    pderiv j (inverseLinearSubstitution U (X i)) = C (U⁻¹ i j) := by
  simp [inverseLinearSubstitution, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The entrywise chain rule for the actual inverse linear substitution. -/
theorem pderiv_inverseLinearSubstitution (f : MvPolynomial n R) (j : n) :
    pderiv j (inverseLinearSubstitution U f) =
      ∑ i, C (U⁻¹ i j) * inverseLinearSubstitution U (pderiv i f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [inverseLinearSubstitution]
  | add f g hf hg =>
      simp only [map_add, hf, hg, mul_add, Finset.sum_add_distrib]
  | mul_X f l hf =>
      have hfirst :
          (∑ i, C (U⁻¹ i j) *
            (inverseLinearSubstitution U (pderiv i f) * inverseLinearSubstitution U (X l))) =
          (∑ i, C (U⁻¹ i j) * inverseLinearSubstitution U (pderiv i f)) *
            inverseLinearSubstitution U (X l) := by
        simp only [← mul_assoc, Finset.sum_mul]
      have hdelta :
          (∑ i, C (U⁻¹ i j) *
            (inverseLinearSubstitution U f * inverseLinearSubstitution U (pderiv i (X l)))) =
          C (U⁻¹ l j) * inverseLinearSubstitution U f := by
        simp [pderiv_X, Pi.single_apply]
      rw [map_mul, pderiv_mul, hf, pderiv_inverseLinearSubstitution_X]
      simp_rw [pderiv_mul, map_add, map_mul, mul_add]
      rw [Finset.sum_add_distrib, hfirst, hdelta]
      ring

/-- Evaluating at the genuinely changed generators gives the exact Jacobian entry formula.
Thus variables-row Jacobians transform by the transpose of this same inverse matrix. -/
theorem aeval_pderiv_inverseLinearSubstitution (P : Generators R B n)
    (hU : IsUnit U.det) (f : MvPolynomial n R) (j : n) :
    aeval (P.linearChange U hU).val (pderiv j (inverseLinearSubstitution U f)) =
      ∑ i, algebraMap R B (U⁻¹ i j) * aeval P.val (pderiv i f) := by
  have heval (q : MvPolynomial n R) :
      aeval (P.linearChange U hU).val (inverseLinearSubstitution U q) = aeval P.val q :=
    DFunLike.congr_fun (aeval_comp_inverseLinearSubstitution P U hU) q
  rw [pderiv_inverseLinearSubstitution]
  simp only [map_sum, map_mul, aeval_C, heval]

end Algebra.Generators
