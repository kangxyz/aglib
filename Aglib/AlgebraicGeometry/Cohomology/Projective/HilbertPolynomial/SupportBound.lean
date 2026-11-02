/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.SupportZero

/-!
# Hilbert polynomial degree is bounded by actual support dimension

Over an infinite field, a coherent module supported in dimension at most
`d` has an integer binomial Hilbert expansion with `d + 1` coefficients.
The proof inducts on the actual support dimension. A native monic
hyperplane map has lower-dimensional cokernel; its exact Hilbert finite
difference is integrated by the integer binomial recurrence. At dimension
zero that cokernel vanishes and the original Hilbert function is constant.

Consequently the native Hilbert polynomial has degree at most `d`.
Equality and the ample positivity needed for it remain separate assertions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (k : Type u) [Field k] (ι : Type u)

/-- The native polynomial difference for a monic tensor twist computes
the same exact integer difference of original Euler characteristics. -/
theorem projectiveHilbertFunction_cokernel_mono_twist
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace k ι).Modules)
    (hF : affineLocallyFiniteType _ F) (a : ℤ)
    (ν : F ⟶ (moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι a)).obj F)
    [Mono ν] (m : ℤ) :
    projectiveHilbertFunction k ι (cokernel ν) m =
      projectiveHilbertFunction k ι F (m + a) - projectiveHilbertFunction k ι F m := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  have hC := (affineLocallyFiniteType (ProjectiveSpace k ι)).prop_cokernel ν hF
    (twistingTensor_affineLocallyFiniteType k ι a F hF)
  have h := congrArg (fun P : ℚ[X] => P.eval (m : ℚ))
    (projectiveHilbertPolynomial_cokernel_mono_twist k ι n e F hF a ν)
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C] at h
  rw [← Int.cast_add,
    ← projectiveHilbertFunction_eq_eval k ι n e (cokernel ν) hC m,
    ← projectiveHilbertFunction_eq_eval k ι n e F hF (m + a),
    ← projectiveHilbertFunction_eq_eval k ι n e F hF m] at h
  exact_mod_cast h

/-- Actual support dimension bounds the integer binomial expansion of
the original coherent Hilbert function over an infinite field. -/
theorem exists_projectiveHilbertFunction_eq_sum_choose_of_supportDimension_le
    [Infinite k] (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℕ) :
    ∀ (F : (ProjectiveSpace k ι).Modules), affineLocallyFiniteType _ F →
      topologicalKrullDim (support F) ≤ (d : ℕ) →
        ∃ a : Fin (d + 1) → ℤ, ∀ m : ℤ,
          projectiveHilbertFunction k ι F m =
            ∑ i : Fin (d + 1), a i * Ring.choose m i := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  induction d with
  | zero =>
    intro F hF hd
    obtain ⟨s, hmono, -⟩ := exists_mono_hyperplane_hilbertDifference k ι n e F hF
    let ν := (twistingTensorZeroIso k ι).inv.app F ≫
      (twistingTensorMultiply k ι ((1 : ℕ) : ℤ) 0 s).app F
    let : Mono ν := hmono
    let C := cokernel ν
    have hCzero : IsZero C :=
      isZero_cokernel_mono_twist_of_supportDimension_nonpos k ι F hF
        (((1 : ℕ) : ℤ) + 0) ν hd
    have hzero (m : ℤ) : projectiveHilbertFunction k ι C m = 0 :=
      projectiveEulerChar_of_isZero k ι
        ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι m)).map_isZero hCzero)
    have hstep (m : ℤ) :
        projectiveHilbertFunction k ι F (m + 1) = projectiveHilbertFunction k ι F m := by
      have hdiff := projectiveHilbertFunction_cokernel_mono_twist k ι n e F hF
        (((1 : ℕ) : ℤ) + 0) ν m
      have hz : projectiveHilbertFunction k ι F (m + 1) -
          projectiveHilbertFunction k ι F m = 0 := by
        simpa using hdiff.symm.trans (hzero m)
      exact sub_eq_zero.mp hz
    have hconst (m : ℤ) :
        projectiveHilbertFunction k ι F m = projectiveHilbertFunction k ι F 0 := by
      induction m using Int.induction_on with
      | zero => rfl
      | succ j ih => exact (hstep (j : ℤ)).trans ih
      | pred j ih =>
        have hj := hstep (-(j : ℤ) - 1)
        rw [sub_add_cancel] at hj
        exact hj.symm.trans ih
    refine ⟨fun _ : Fin 1 => projectiveHilbertFunction k ι F 0, fun m => ?_⟩
    change projectiveHilbertFunction k ι F m =
      ∑ i : Fin 1, projectiveHilbertFunction k ι F 0 * Ring.choose m i
    rw [Fin.sum_univ_one]
    simpa only [Fin.val_zero, Ring.choose_zero_right, mul_one] using hconst m
  | succ d ih =>
    intro F hF hd
    obtain ⟨s, hmono, -⟩ := exists_mono_hyperplane_hilbertDifference k ι n e F hF
    let ν := (twistingTensorZeroIso k ι).inv.app F ≫
      (twistingTensorMultiply k ι ((1 : ℕ) : ℤ) 0 s).app F
    let : Mono ν := hmono
    let C := cokernel ν
    have hC : affineLocallyFiniteType (ProjectiveSpace k ι) C :=
      (affineLocallyFiniteType (ProjectiveSpace k ι)).prop_cokernel ν hF
        (twistingTensor_affineLocallyFiniteType k ι (((1 : ℕ) : ℤ) + 0) F hF)
    have hdC : topologicalKrullDim (support C) ≤ (d : ℕ) :=
      topologicalKrullDim_support_cokernel_mono_twist_le k ι F hF
        (((1 : ℕ) : ℤ) + 0) ν d hd
    obtain ⟨a, ha⟩ := ih C hC hdC
    have hdiff (m : ℤ) :
        projectiveHilbertFunction k ι F (m + 1) - projectiveHilbertFunction k ι F m =
          projectiveHilbertFunction k ι C m := by
      simpa using (projectiveHilbertFunction_cokernel_mono_twist k ι n e F hF
        (((1 : ℕ) : ℤ) + 0) ν m).symm
    exact ⟨_, Int.eq_sum_choose_of_fwdDiff a (fun m => (hdiff m).trans (ha m))⟩

/-- The degree of the actual coherent Hilbert polynomial is at most the
dimension bound for its original support, over an infinite field. -/
theorem natDegree_projectiveHilbertPolynomial_le_of_supportDimension_le
    [Infinite k] (n : ℕ) (e : ι ≃ Fin (n + 1)) (d : ℕ)
    (F : (ProjectiveSpace k ι).Modules) (hF : affineLocallyFiniteType _ F)
    (hd : topologicalKrullDim (support F) ≤ (d : ℕ)) :
    (projectiveHilbertPolynomial k ι F).natDegree ≤ d := by
  obtain ⟨a, ha⟩ :=
    exists_projectiveHilbertFunction_eq_sum_choose_of_supportDimension_le k ι n e d F hF hd
  have hP : projectiveHilbertPolynomial k ι F = ∑ i : Fin (d + 1),
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
  rw [hP]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [descPochhammer_natDegree]
  exact Nat.lt_succ_iff.mp i.2

end AlgebraicGeometry.Scheme.Cohomology
