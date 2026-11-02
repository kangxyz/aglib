/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Blowup.QuadraticPresentation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Original quadratic Case-I/Case-II dichotomy

The fixed-coordinate dehomogenization detects homogeneous quadratic scalar
squares. Its exact coefficient calculation works over every field. A nonzero
scalar is removed only from the principal ideal, never by taking a square root.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open scoped BigOperators
open MvPolynomial

universe u

namespace GradedAlgebra.TernaryQuadratic

variable {k : Type u} [Field k]

theorem eq_quadratic_of_homogeneous {q : MvPolynomial (Fin 3) k}
    (hq : q.IsHomogeneous 2) : q = quadratic (fun i => q.coeff (exponent i)) := by
  classical
  ext d
  by_cases hd : d.degree = 2
  · have hsum : d.degree = d 0 + d 1 + d 2 := by
      change d.sum (fun _ n => n) = _
      rw [Finsupp.sum_fintype _ _ (by intro i; rfl)]
      simp [Fin.sum_univ_succ, add_assoc]
    have hcases : (d 0 = 2 ∧ d 1 = 0 ∧ d 2 = 0) ∨
        (d 0 = 0 ∧ d 1 = 2 ∧ d 2 = 0) ∨
        (d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 2) ∨
        (d 0 = 1 ∧ d 1 = 1 ∧ d 2 = 0) ∨
        (d 0 = 1 ∧ d 1 = 0 ∧ d 2 = 1) ∨
        (d 0 = 0 ∧ d 1 = 1 ∧ d 2 = 1) := by omega
    have hex : ∃ i, d = exponent i := by
      rcases hcases with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
        ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
      · refine ⟨0, ?_⟩; ext i; fin_cases i <;> simp [exponent, h0, h1, h2]
      · refine ⟨1, ?_⟩; ext i; fin_cases i <;> simp [exponent, h0, h1, h2]
      · refine ⟨2, ?_⟩; ext i; fin_cases i <;> simp [exponent, h0, h1, h2]
      · refine ⟨3, ?_⟩; ext i; fin_cases i <;> simp [exponent, h0, h1, h2]
      · refine ⟨4, ?_⟩; ext i; fin_cases i <;> simp [exponent, h0, h1, h2]
      · refine ⟨5, ?_⟩; ext i; fin_cases i <;> simp [exponent, h0, h1, h2]
    obtain ⟨i, rfl⟩ := hex
    exact (quadratic_coeff (fun j => q.coeff (exponent j)) i).symm
  · rw [hq.coeff_eq_zero hd, (quadratic_homogeneous _).coeff_eq_zero hd]

end GradedAlgebra.TernaryQuadratic

namespace MvPolynomial.FirstCoordinate

open GradedAlgebra.TernaryQuadratic

variable {k : Type u} [Field k]

/-- The existing first-coordinate dehomogenization loses no coefficient in
fixed homogeneous degree two. -/
theorem dehom_injective_on_homogeneous_two {p q : MvPolynomial (Fin 3) k}
    (hp : p.IsHomogeneous 2) (hq : q.IsHomogeneous 2) (h : dehom p = dehom q) :
    p = q := by
  have hp' := GradedAlgebra.TernaryQuadratic.eq_quadratic_of_homogeneous hp
  have hq' := GradedAlgebra.TernaryQuadratic.eq_quadratic_of_homogeneous hq
  rw [hp', hq'] at h
  have hc : (fun i => p.coeff (exponent i)) = (fun i => q.coeff (exponent i)) := by
    funext i
    simpa only [dehom_quadratic_coeff] using
      congrArg (fun f : MvPolynomial (Fin 2) k => f.coeff (affineExponent i)) h
  exact hp'.trans ((congrArg quadratic hc).trans hq'.symm)

private theorem affine_linear_expansion (l : MvPolynomial (Fin 2) k)
    (hl : l.totalDegree ≤ 1) :
    ∃ a b c : k, l = QuadraticClosedPoint.linear a b c := by
  have hz (d : Fin 2 →₀ ℕ) (hd : (∑ i ∈ d.support, d i) = 2) : l.coeff d = 0 :=
    coeff_eq_zero_of_totalDegree_lt (by rw [hd]; omega)
  have h20 := hz (Finsupp.single 0 2) (by simp)
  have h02 := hz (Finsupp.single 1 2) (by simp)
  have h11 := hz (Finsupp.single 1 1 + Finsupp.single 0 1) (by
    change (Finsupp.single (1 : Fin 2) 1 + Finsupp.single 0 1).degree = 2
    simp)
  refine ⟨l.coeff 0, l.coeff (Finsupp.single 1 1), l.coeff (Finsupp.single 0 1), ?_⟩
  have h := QuadraticClosedPoint.eq_quadratic_of_totalDegree_le l (by omega)
  simpa only [h20, h02, h11, QuadraticClosedPoint.quadratic,
    QuadraticClosedPoint.linear, map_zero, zero_mul, add_zero] using h

private theorem dehom_linear_totalDegree {L : MvPolynomial (Fin 3) k}
    (hL : L.IsHomogeneous 1) : (dehom L).totalDegree ≤ 1 := by
  classical
  have hmem : L ∈ Submodule.span k (Set.range (X : Fin 3 → MvPolynomial (Fin 3) k)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hL
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp hmem
  have he : dehom L = QuadraticClosedPoint.linear (c 0) (c 2) (c 1) := by
    rw [← hc, Fin.sum_univ_three]
    simp only [Algebra.smul_def, algebraMap_eq, map_add, map_mul, dehom_C,
      dehom_X_zero, show (1 : Fin 3) = (0 : Fin 2).succ from rfl,
      show (2 : Fin 3) = (1 : Fin 2).succ from rfl, dehom_X_succ, mul_one,
      QuadraticClosedPoint.linear]
    ring
  rw [he]
  exact QuadraticClosedPoint.linear_totalDegree _ _ _

/-- The exact affine Case-I exception is equivalent to a homogeneous scalar
linear square over the same original field, in every characteristic. -/
theorem scalar_linear_square_iff {q : MvPolynomial (Fin 3) k}
    (hq : q.IsHomogeneous 2) (hq0 : q ≠ 0) :
    (∃ c : k, c ≠ 0 ∧ ∃ l : MvPolynomial (Fin 2) k,
      l.totalDegree ≤ 1 ∧ dehom q = C c * l ^ 2) ↔
    (∃ c : k, c ≠ 0 ∧ ∃ L : MvPolynomial (Fin 3) k,
      L.IsHomogeneous 1 ∧ L ≠ 0 ∧ q = C c * L ^ 2) := by
  constructor
  · rintro ⟨c, hc, l, hl, he⟩
    obtain ⟨a, b, d, rfl⟩ := affine_linear_expansion l hl
    let L : MvPolynomial (Fin 3) k := C a * X 0 + C b * X 2 + C d * X 1
    have hL : L.IsHomogeneous 1 :=
      (((isHomogeneous_X (R := k) 0).C_mul a).add
        ((isHomogeneous_X (R := k) 2).C_mul b)).add
          ((isHomogeneous_X (R := k) 1).C_mul d)
    have hdehom : dehom L = QuadraticClosedPoint.linear a b d := by
      simp only [L, QuadraticClosedPoint.linear, map_add, map_mul, dehom_C,
        dehom_X_zero, show (1 : Fin 3) = (0 : Fin 2).succ from rfl,
        show (2 : Fin 3) = (1 : Fin 2).succ from rfl, dehom_X_succ, mul_one]
    have heq : q = C c * L ^ 2 := by
      apply dehom_injective_on_homogeneous_two hq ((hL.pow 2).C_mul c)
      rw [map_mul, map_pow, dehom_C, hdehom]
      exact he
    refine ⟨c, hc, L, hL, ?_, heq⟩
    intro hzero
    apply hq0
    rw [heq, hzero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
  · rintro ⟨c, hc, L, hL, _, rfl⟩
    exact ⟨c, hc, dehom L, dehom_linear_totalDegree hL,
      by rw [map_mul, map_pow, dehom_C]⟩

/-- Every original nonzero homogeneous quadratic gives the exact Case-I
predicate or a full principal linear-square ideal. Scalars are removed by a
unit ideal identity, not by extracting a square root. -/
theorem caseOne_or_linearSquare_span {q : MvPolynomial (Fin 3) k}
    (hq : q.IsHomogeneous 2) (hq0 : q ≠ 0) :
    (¬ ∃ c : k, c ≠ 0 ∧ ∃ l : MvPolynomial (Fin 2) k,
      l.totalDegree ≤ 1 ∧ dehom q = C c * l ^ 2) ∨
    ∃ L : MvPolynomial (Fin 3) k, L.IsHomogeneous 1 ∧ L ≠ 0 ∧
      Ideal.span {q} = Ideal.span {L ^ 2} := by
  by_cases h : ∃ c : k, c ≠ 0 ∧ ∃ l : MvPolynomial (Fin 2) k,
      l.totalDegree ≤ 1 ∧ dehom q = C c * l ^ 2
  · obtain ⟨c, hc, L, hL, hL0, he⟩ := (scalar_linear_square_iff hq hq0).mp h
    refine Or.inr ⟨L, hL, hL0, ?_⟩
    rw [he]
    exact Ideal.span_singleton_mul_left_unit ((isUnit_iff_ne_zero.mpr hc).map C) _
  · exact Or.inl h

end MvPolynomial.FirstCoordinate
