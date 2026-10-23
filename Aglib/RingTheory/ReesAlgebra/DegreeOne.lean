/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.ReesAlgebra.Away
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct

/-!
# Degree-one generation of the original Rees algebra and its scalar extension

The powers of the original degree-one submodule are exactly the original
homogeneous components, including degree zero. Scalar extension preserves
these equalities in the full tensor algebra. No flatness, domain or
Noetherianity hypothesis is used. The current consumer is the graded
polynomial presentation of a base-changed blowup.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace reesAlgebra

variable {A : Type u} [CommRing A]

private theorem homogeneous_succ_mem_grading_one_pow (I : Ideal A) (n : ℕ)
    (hn : (grading I 1) ^ n = grading I n) (b : A) (hb : b ∈ I ^ (n + 1)) :
    (homogeneous I (n + 1) ⟨b, hb⟩ : reesAlgebra I) ∈ (grading I 1) ^ (n + 1) := by
  refine Submodule.smul_induction_on'
    (p := fun b hb => (homogeneous I (n + 1) ⟨b, by rwa [pow_succ']⟩ : reesAlgebra I) ∈
      (grading I 1) ^ (n + 1)) (by rwa [pow_succ'] at hb) ?_ ?_
  · intro x hx y hy
    have he : (homogeneous I (n + 1)
        ⟨x * y, by rw [pow_succ']; exact Ideal.mul_mem_mul hx hy⟩ : reesAlgebra I) =
        degreeOne I ⟨x, hx⟩ * homogeneous I n ⟨y, hy⟩ := by
      apply Subtype.ext
      change monomial (n + 1) (x * y) = monomial 1 x * monomial n y
      rw [monomial_mul_monomial, Nat.add_comm n 1]
    change (homogeneous I (n + 1) ⟨x * y, _⟩ : reesAlgebra I) ∈ _
    rw [he, pow_succ', hn]
    exact Submodule.mul_mem_mul (degreeOne_mem I ⟨x, hx⟩)
      (homogeneous I n ⟨y, hy⟩).property
  · intro x hx y hy ihx ihy
    have he : (homogeneous I (n + 1)
        ⟨x + y, by rw [pow_succ']; exact Ideal.add_mem _ hx hy⟩ : reesAlgebra I) =
        homogeneous I (n + 1) ⟨x, by rwa [pow_succ']⟩ +
          homogeneous I (n + 1) ⟨y, by rwa [pow_succ']⟩ := by
      apply Subtype.ext
      exact map_add (monomial (n + 1)) x y
    rw [he]
    exact Submodule.add_mem _ ihx ihy

/-- The original Rees algebra is generated in degree one, including degree zero. -/
theorem grading_one_pow (I : Ideal A) (n : ℕ) :
    (grading I 1) ^ n = grading I n := by
  induction n with
  | zero =>
    rw [pow_zero]
    apply le_antisymm
    · exact Submodule.one_le.mpr (SetLike.one_mem_graded (grading I))
    · intro p hp
      rw [Submodule.one_eq_span]
      have he : p = algebraMap A (reesAlgebra I) ((p : A[X]).coeff 0) := by
        apply Subtype.ext
        exact (eq_monomial_coeff hp).trans
          (Polynomial.monomial_zero_left (a := (p : A[X]).coeff 0))
      rw [he]
      simpa only [Algebra.smul_def, mul_one] using
        (Submodule.smul_mem (Submodule.span A ({1} : Set (reesAlgebra I)))
          ((p : A[X]).coeff 0) (Submodule.subset_span (Set.mem_singleton 1)))
  | succ n ih =>
    apply le_antisymm
    · rw [pow_succ', ih]
      exact Submodule.mul_le.mpr fun p hp q hq => by
        simpa only [Nat.add_comm 1 n] using SetLike.mul_mem_graded hp hq
    · intro p hp
      have he : p = (homogeneous I (n + 1)
          ⟨(p : A[X]).coeff (n + 1), p.property _⟩ : reesAlgebra I) := by
        apply Subtype.ext
        exact eq_monomial_coeff hp
      rw [he]
      exact homogeneous_succ_mem_grading_one_pow I n ih _ _

end reesAlgebra

namespace Submodule

open TensorProduct

variable {R S C : Type u} [CommRing R] [CommRing S] [CommRing C]
  [Algebra R S] [Algebra R C]

/-- Scalar extension preserves products of submodules of the original algebra. -/
private theorem baseChange_mul_eq (M N : Submodule R C) :
    (M * N).baseChange S = M.baseChange S * N.baseChange S := by
  simp only [baseChange_eq_span]
  change Submodule.span S
      (((M * N).map (Algebra.TensorProduct.includeRight : C →ₐ[R] S ⊗[R] C).toLinearMap) :
        Set (S ⊗[R] C)) =
    Submodule.span S
      ((M.map (Algebra.TensorProduct.includeRight : C →ₐ[R] S ⊗[R] C).toLinearMap) :
        Set (S ⊗[R] C)) *
      Submodule.span S
        ((N.map (Algebra.TensorProduct.includeRight : C →ₐ[R] S ⊗[R] C).toLinearMap) :
          Set (S ⊗[R] C))
  rw [Submodule.map_mul, Submodule.mul_def, Submodule.span_span_of_tower,
    Submodule.span_mul_span]

private theorem baseChange_one_eq : (1 : Submodule R C).baseChange S = 1 := by
  rw [baseChange_eq_span]
  change Submodule.span S
    (((1 : Submodule R C).map
      (Algebra.TensorProduct.includeRight : C →ₐ[R] S ⊗[R] C).toLinearMap) :
        Set (S ⊗[R] C)) = 1
  rw [Submodule.map_one, Submodule.one_eq_span, Submodule.span_span_of_tower,
    ← Submodule.one_eq_span]

private theorem baseChange_pow_eq (M : Submodule R C) (n : ℕ) :
    (M ^ n).baseChange S = M.baseChange S ^ n := by
  induction n with
  | zero => simp only [pow_zero, baseChange_one_eq]
  | succ n ih => rw [pow_succ, baseChange_mul_eq, ih, pow_succ]

end Submodule

namespace reesAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Full scalar extension of the Rees algebra remains generated in degree one.
The tensor coefficients are retained; no image in `S[t]` is used. -/
theorem baseChange_grading_one_pow (I : Ideal R) (n : ℕ) :
    ((grading I 1).baseChange S) ^ n = (grading I n).baseChange S := by
  rw [← Submodule.baseChange_pow_eq, grading_one_pow]

end reesAlgebra
