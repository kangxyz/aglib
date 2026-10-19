/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Basic

/-!
# The degree of the Hilbert polynomial on `P^n_k`

The Hilbert polynomial of a coherent sheaf on `P^n_k` has degree at most `n`
(`natDegree_projectiveHilbertPolynomial_le`): by `exists_projectiveHilbertFunction_eq_sum_choose`,
`χ(F(m)) = Σ_{i ≤ n} aᵢ C(m, i)`, and `C(m, i)` is the value of the polynomial
`descPochhammer i / i!` of degree `i`. This is the degree bound behind the re-indexing of the
flattening stratification by `n + 1` values (Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, proof of Thm 4.3, p. 22).
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- **The Hilbert polynomial of a coherent sheaf on `P^n_k` has degree at most `n`** (Nitsure,
arXiv:math/0504590v1, proof of Thm 4.3, p. 22): `χ(F(m)) = Σ_{i ≤ n} aᵢ C(m, i)`, and `C(m, i)`
is the value of the polynomial `descPochhammer i / i!` of degree `i`. -/
theorem natDegree_projectiveHilbertPolynomial_le {k : Type u} [Field k] {ι : Type u} (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace k ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) :
    (projectiveHilbertPolynomial k ι F).natDegree ≤ n := by
  obtain ⟨a, ha⟩ := exists_projectiveHilbertFunction_eq_sum_choose k ι n e F hF
  have hΦ : projectiveHilbertPolynomial k ι F = ∑ i : Fin (n + 1),
      Polynomial.C ((a i : ℚ) / ((i : ℕ).factorial : ℚ)) * descPochhammer ℚ i := by
    refine projectiveHilbertPolynomial_eq_of_eval k ι F fun m => ?_
    rw [ha m, Polynomial.eval_finsetSum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, ← descPochhammer_eval_cast,
      Polynomial.eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
    have hfac : ((i : ℕ).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [hΦ]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [descPochhammer_natDegree]
  exact Nat.lt_succ_iff.mp i.2

end AlgebraicGeometry.Scheme.Cohomology
