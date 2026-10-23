/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Localization.Integer

/-!
# Polynomial coordinates in a rational-function-field basis

The bounded polynomial ansatz in a finite basis is injective. Consequently a
nonzero tuple of scalar parameters cannot produce the zero field element.
Denominator clearing uses the native localization theorem, not a choice of
separate denominators that could invalidate a degree bound.
-/

@[expose] public section

open scoped Polynomial

namespace Module.Basis

variable {K E ι : Type*} [Field K] [Field E] [Algebra (RatFunc K) E] [Fintype ι]

open Classical in
/-- Polynomial coordinates of bounded length in a rational-function-field basis
are uniquely determined by their resulting field element. -/
theorem polynomialCoordinates_injective (b : Basis ι (RatFunc K) E) (m : ℕ) :
    Function.Injective (fun a : ι → Fin m → K =>
      ∑ i, algebraMap K[X] (RatFunc K) (Polynomial.ofFn m (a i)) • b i) := by
  classical
  intro a a' h
  have hrepr := congrArg (fun z => (b.repr z : ι → RatFunc K)) h
  simp only [b.repr_sum_self] at hrepr
  funext i
  apply Polynomial.injective_ofFn m
  apply RatFunc.algebraMap_injective
  exact congrFun hrepr i

open Classical in
/-- Nonzero polynomial-coordinate data stay nonzero after the basis ansatz. -/
theorem polynomialCoordinates_ne_zero (b : Basis ι (RatFunc K) E) (m : ℕ)
    (a : ι → Fin m → K) (ha : a ≠ 0) :
    (∑ i, algebraMap K[X] (RatFunc K) (Polynomial.ofFn m (a i)) • b i) ≠ 0 := by
  classical
  intro h
  apply ha
  apply b.polynomialCoordinates_injective m
  simpa using h

end Module.Basis

namespace RatFunc

/-- One nonzero polynomial simultaneously clears all denominators in a finite
family of rational functions. -/
theorem exists_common_polynomial_denominator {K ι : Type*} [Field K] [Finite ι]
    (f : ι → RatFunc K) :
    ∃ q : K[X], q ≠ 0 ∧ ∃ a : ι → K[X],
      ∀ i, algebraMap K[X] (RatFunc K) (a i) = algebraMap K[X] (RatFunc K) q * f i := by
  obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors K[X]) f
  choose a ha using hq
  exact ⟨q, nonZeroDivisors.ne_zero q.property, a, fun i => by
    simpa only [Algebra.smul_def] using ha i⟩

end RatFunc
