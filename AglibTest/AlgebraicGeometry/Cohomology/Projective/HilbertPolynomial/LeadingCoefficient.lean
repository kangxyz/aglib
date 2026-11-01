/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.LeadingCoefficient

/-! Native numerical consumers retain degree zero and level one. -/

@[expose] public noncomputable section

open scoped Polynomial

example {P : ℚ[X]} (hP : P ≠ 0) (r : ℕ) (hd : P.natDegree = 0)
    (h : (P.comp (Polynomial.C (9 : ℚ) * Polynomial.X)).leadingCoeff =
      (r : ℚ) * P.leadingCoeff) : r = 1 := by
  simpa using Polynomial.nat_eq_pow_of_leadingCoeff_comp_C_mul_X hP 9 r 0 (by decide) hd h

example {P : ℚ[X]} (hP : P ≠ 0) (r d : ℕ) (hd : P.natDegree = d)
    (h : P.leadingCoeff = (r : ℚ) * P.leadingCoeff) : r = 1 := by
  have h' : (P.comp (Polynomial.C (1 : ℚ) * Polynomial.X)).leadingCoeff =
      (r : ℚ) * P.leadingCoeff := by simpa using h
  simpa using Polynomial.nat_eq_pow_of_leadingCoeff_comp_C_mul_X hP 1 r d (by decide) hd h'

example {P : ℚ[X]} (hP : P ≠ 0) (n r d : ℕ) (hn : 0 < n) (hd : P.natDegree = d)
    (h : (P.comp (Polynomial.C ((n : ℚ) ^ 2) * Polynomial.X)).leadingCoeff =
      (r : ℚ) * P.leadingCoeff) : r = n ^ (2 * d) := by
  have h' : (P.comp (Polynomial.C ((n ^ 2 : ℕ) : ℚ) * Polynomial.X)).leadingCoeff =
      (r : ℚ) * P.leadingCoeff := by simpa using h
  simpa [pow_mul] using Polynomial.nat_eq_pow_of_leadingCoeff_comp_C_mul_X
    hP (n ^ 2) r d (pow_pos hn 2) hd h'

end
