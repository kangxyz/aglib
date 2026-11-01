/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.BoundedParameters.Points

/-!
# The actual tuple decomposition of a repeated effective divisor

Remove two copies of a point whose coefficient is at least two and apply
the existing ordered-point decomposition to the remaining effective
divisor. This gives precisely the duplicated-first-coordinate shape used
by the original repeated Abel morphism. Degree zero for the remainder is
allowed, and no symmetric-power or new divisor realization is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard

open Divisors Degree

variable {k : Type u} [Field k] [IsAlgClosed k]
  (Y : Scheme.{u}) (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p]

/-- An effective degree-(n+2) divisor with a repeated point has the exact
duplicated-first-coordinate tuple shape, preserving all multiplicities. -/
theorem effective_divisor_eq_repeated_tuple (n : ℕ) (D : Divisor Y)
    (heff : ∀ x, 0 ≤ D x) (hdeg : degDiv Y p D = ((n + 2 : ℕ) : ℤ))
    (hrep : ∃ x, 2 ≤ D x) :
    ∃ s : Fin (n + 1) → ClosedPoint Y,
      D = Finsupp.single (s 0) 1 + ∑ i, Finsupp.single (s i) 1 := by
  classical
  obtain ⟨x, hx⟩ := hrep
  let A : Divisor Y := Finsupp.single x 1
  let E : Divisor Y := D - (A + A)
  have hE : ∀ y, 0 ≤ E y := by
    intro y
    by_cases hy : y = x
    · subst y
      simp only [E, A, Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    · simpa only [E, A, Finsupp.sub_apply, Finsupp.add_apply,
        Finsupp.single_eq_of_ne hy, add_zero, sub_zero] using heff y
  have hA : degDiv Y p A = 1 := by
    simp only [A, degDiv_single, weight_eq_one, mul_one]
  have hEdeg : degDiv Y p E = (n : ℤ) := by
    dsimp only [E]
    rw [map_sub, map_add, hA, hdeg]
    push_cast
    ring
  obtain ⟨t, ht⟩ := effective_divisor_eq_sum_points Y p n E hE hEdeg
  let s : Fin (n + 1) → ClosedPoint Y := Fin.cases x t
  refine ⟨s, ?_⟩
  simp only [s, Fin.cases_zero, Fin.sum_univ_succ, Fin.cases_succ]
  rw [← ht]
  change D = A + (A + (D - (A + A)))
  abel

/-- The same decomposition from failure of simplicity, using actual
nonnegative integer coefficients rather than point cardinality. -/
theorem effective_divisor_eq_repeated_tuple_of_not_simple (n : ℕ) (D : Divisor Y)
    (heff : ∀ x, 0 ≤ D x) (hdeg : degDiv Y p D = ((n + 2 : ℕ) : ℤ))
    (hsimple : ¬ ∀ x, D x = 0 ∨ D x = 1) :
    ∃ s : Fin (n + 1) → ClosedPoint Y,
      D = Finsupp.single (s 0) 1 + ∑ i, Finsupp.single (s i) 1 := by
  apply effective_divisor_eq_repeated_tuple Y p n D heff hdeg
  by_contra! h
  apply hsimple
  intro x
  have := heff x
  have := h x
  omega

end AlgebraicGeometry.Scheme.OverField.Curve.Picard
