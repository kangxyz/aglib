/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Tactic.LinearCombination

/-! # Actual Laurent cutoffs and uniform finite windows

The original Laurent truncation is linear over the coefficient ring. Its complementary
positive and negative cutoffs retain the original variable inversion. Multiplying arbitrary
negative-chart polynomials by any fixed Laurent polynomial has a uniformly bounded
nonnegative part. The bound is proved by monomial induction over every commutative ring.
-/

/-!
Source: `quillen-k-theory/Quillen/Aglib/Algebra/Polynomial/Laurent/Cutoff.lean` from the supplied
frozen Quillen snapshot.
SHA-256: `9f70ac9cfbd6b10fef3e2d873500ddcf711631699fe032453f54c5f5d5cfd19f`.
Only native objects, maps and mathematical namespaces are used in this extraction.
-/

@[expose] public section

noncomputable section
open Polynomial LaurentPolynomial
open scoped LaurentPolynomial
universe u
namespace LaurentPolynomial.Cutoff
variable (R : Type u) [CommRing R]

/-- The original Laurent truncation, with its actual scalar action. -/
def truncLinear : R[T;T⁻¹] →ₗ[R] R[X] where
  toFun := trunc
  map_add' := trunc.map_add
  map_smul' a p := by
    induction p using LaurentPolynomial.induction_on' with
    | add p q hp hq => simp only [smul_add, map_add, hp, hq]
    | C_mul_T n b =>
      rw [LaurentPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul, trunc_C_mul_T]
      by_cases hn : 0 ≤ n <;> simp [trunc_C_mul_T, hn, Polynomial.smul_monomial]

/-- The original nonnegative Laurent projection. -/
def nonnegative : R[T;T⁻¹] →ₗ[R] R[T;T⁻¹] :=
  Polynomial.toLaurentAlg.toLinearMap.comp (truncLinear R)

/-- The original nonpositive projection, obtained by actual variable inversion. -/
def nonpositive : R[T;T⁻¹] →ₗ[R] R[T;T⁻¹] :=
  LaurentPolynomial.invert.toLinearMap.comp
    ((nonnegative R).comp LaurentPolynomial.invert.toLinearMap)

/-- The strictly negative projection complementary to the nonnegative one. -/
def negative : R[T;T⁻¹] →ₗ[R] R[T;T⁻¹] := LinearMap.id - nonnegative R

/-- The strictly positive projection complementary to the nonpositive one. -/
def positive : R[T;T⁻¹] →ₗ[R] R[T;T⁻¹] := LinearMap.id - nonpositive R

end LaurentPolynomial.Cutoff

namespace LaurentPolynomial.Cutoff
variable {R : Type u} [CommRing R]

/-- The original nonnegative cutoff keeps exactly its specified Laurent monomials. -/
theorem nonnegative_monomial (k : ℤ) (a : R) :
    nonnegative R (LaurentPolynomial.C a * T k) =
      if 0 ≤ k then LaurentPolynomial.C a * T k else 0 := by
  by_cases h : 0 ≤ k <;>
    simp [nonnegative, truncLinear, trunc_C_mul_T, h]

/-- Actual variable inversion gives the nonpositive cutoff on original monomials. -/
theorem nonpositive_monomial (k : ℤ) (a : R) :
    nonpositive R (LaurentPolynomial.C a * T k) =
      if k ≤ 0 then LaurentPolynomial.C a * T k else 0 := by
  change invert (nonnegative R (invert (LaurentPolynomial.C a * T k))) = _
  simp only [map_mul, invert_C, invert_T, nonnegative_monomial]
  by_cases h : k ≤ 0 <;> simp [h]

/-- The original strictly negative remainder is recovered by the nonpositive cutoff. -/
theorem nonpositive_negative (p : R[T;T⁻¹]) :
    nonpositive R (negative R p) = negative R p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | C_mul_T k a =>
    simp only [negative, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
    rw [nonnegative_monomial, nonpositive_monomial]
    by_cases h : 0 ≤ k
    · simp [h, nonpositive_monomial]
    · have hk : k ≤ 0 := by omega
      simp [h, hk]

/-- The positive cutoff ignores the original negative remainder. -/
theorem positive_nonnegative (p : R[T;T⁻¹]) :
    positive R (nonnegative R p) = positive R p := by
  have h := nonpositive_negative p
  change nonpositive R (p - nonnegative R p) = p - nonnegative R p at h
  rw [map_sub] at h
  change nonnegative R p - nonpositive R (nonnegative R p) = p - nonpositive R p
  linear_combination h

end LaurentPolynomial.Cutoff

namespace LaurentPolynomial.Cutoff
variable {R : Type u} [CommRing R]

/-- A fixed Laurent monomial sends every negative-chart polynomial into one finite window. -/
theorem trunc_monomial_negative_mem (k : ℤ) (a : R) (b : R[X]) :
    trunc (LaurentPolynomial.C a * T k * invert (toLaurent b)) ∈
      Polynomial.degreeLT R (k.toNat + 1) := by
  induction b using Polynomial.induction_on' with
  | add b c hb hc =>
    simpa only [map_add, mul_add] using (Polynomial.degreeLT R (k.toNat + 1)).add_mem hb hc
  | monomial n c =>
    have he : LaurentPolynomial.C a * T k * invert (toLaurent (Polynomial.monomial n c)) =
        LaurentPolynomial.C (a * c) * T (k - n) := by
      simp only [Polynomial.toLaurent_C_mul_T, map_mul, invert_C, invert_T]
      rw [mul_mul_mul_comm, ← map_mul, ← T_add]
      congr 2
    rw [he, trunc_C_mul_T]
    split_ifs with h
    · apply Polynomial.mem_degreeLT.mpr
      exact (Polynomial.degree_monomial_le _ _).trans_lt
        (by exact_mod_cast (show (k - (n : ℤ)).toNat < k.toNat + 1 by omega))
    · exact (Polynomial.degreeLT R (k.toNat + 1)).zero_mem

/-- Every actual Laurent coefficient has a uniform finite window on negative-chart inputs. -/
theorem exists_trunc_negative_bound (g : R[T;T⁻¹]) :
    ∃ N : ℕ, ∀ b : R[X], trunc (g * invert (toLaurent b)) ∈ Polynomial.degreeLT R N := by
  induction g using LaurentPolynomial.induction_on' with
  | add g h hg hh =>
    obtain ⟨N, hN⟩ := hg
    obtain ⟨M, hM⟩ := hh
    refine ⟨max N M, fun b => ?_⟩
    rw [add_mul, map_add]
    exact (Polynomial.degreeLT R (max N M)).add_mem
      (Polynomial.degreeLT_mono (le_max_left N M) (hN b))
      (Polynomial.degreeLT_mono (le_max_right N M) (hM b))
  | C_mul_T k a => exact ⟨k.toNat + 1, trunc_monomial_negative_mem k a⟩

end LaurentPolynomial.Cutoff
