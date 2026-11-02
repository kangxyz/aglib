/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Finite integral capture over a fraction-field base

Finitely many coefficients in a finite extension of the original fraction
field can be multiplied by one nonzero base element so that they lie in an
actual module-finite base subalgebra. The subalgebra is generated only by
these finitely many integral multiples; no finiteness of the entire integral
closure is assumed. The empty coefficient set is allowed.
-/

@[expose] public noncomputable section

open scoped BigOperators nonZeroDivisors

namespace IsFractionRing

universe u v w

variable (R : Type u) [CommRing R] [IsDomain R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
  {L : Type w} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Module.Finite K L]

include K in
/-- A common nonzero denominator captures finitely many extension-field
coefficients inside one original module-finite base subalgebra. -/
theorem exists_finiteSubalgebra_common_multiple (s : Finset L) :
    ∃ r : R, r ≠ 0 ∧ ∃ B : Subalgebra R L, Module.Finite R B ∧
      ∀ x ∈ s, r • x ∈ B := by
  classical
  have hi (x : L) : ∃ m : R⁰, IsIntegral R (m • x) :=
    IsIntegral.exists_multiple_integral_of_isLocalization R⁰ x
      (Algebra.IsIntegral.isIntegral (R := K) x)
  let m : L → R⁰ := fun x => (hi x).choose
  have hm (x : L) : IsIntegral R ((m x : R) • x) := (hi x).choose_spec
  let r : R := ∏ x ∈ s, (m x : R)
  have hr : r ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x _ =>
    mem_nonZeroDivisors_iff_ne_zero.mp (m x).property
  have hint (x : L) (hx : x ∈ s) : IsIntegral R (r • x) := by
    obtain ⟨a, ha⟩ := Finset.dvd_prod_of_mem (fun y => (m y : R)) hx
    change r = (m x : R) * a at ha
    rw [ha, mul_comm (m x : R) a, mul_smul]
    exact IsIntegral.smul a (hm x)
  let T : Finset L := s.image (fun x => r • x)
  let B : Subalgebra R L := Algebra.adjoin R (T : Set L)
  have hB : Module.Finite R B :=
    Algebra.finite_adjoin_of_finite_of_isIntegral T.finite_toSet (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact hint y hy)
  refine ⟨r, hr, B, hB, ?_⟩
  intro x hx
  exact Algebra.subset_adjoin (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

end IsFractionRing
