/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.AdjugateExpansion
public import Aglib.RingTheory.MvPolynomial.QuadraticRemainder
public import Aglib.RingTheory.Henselian.PolynomialSystem
public import Mathlib.Tactic.Ring

/-!
# Determinant-squared correction over a Henselian local ring

A finite square polynomial system whose error belongs to the determinant
squared times a proper ideal admits an exact solution differing by the
determinant times that ideal. The proof constructs an identity-Jacobian
system and applies actual multivariate Hensel lifting.

The determinant may be zero or a zero divisor; no cancellation is used.
The ideal is arbitrary and proper, and the finite variable type may be empty.
This is a singular correction lemma, not the Artin approximation theorem.
The displayed matrix uses equations as rows and variables as columns.
-/

@[expose] public section

open scoped Matrix

namespace HenselianLocalRing

open MvPolynomial

variable {R σ : Type*} [CommRing R] [HenselianLocalRing R]
    [Fintype σ] [DecidableEq σ]

/-- Determinant-squared correction. The determinant need not be a unit or
regular element. The ideal precision is arbitrary, not only a maximal-ideal power. -/
theorem exists_eval_eq_zero_of_mem_det_sq_mul
    (F : σ → MvPolynomial σ R) (y₀ : σ → R) (a : Ideal R) (ha : a ≠ ⊤)
    (hF : ∀ i, eval y₀ (F i) ∈
      Ideal.span {Matrix.det (Matrix.of fun i j ↦ eval y₀ (pderiv j (F i))) ^ 2} * a) :
    ∃ y : σ → R, (∀ i, eval y (F i) = 0) ∧
      ∀ i, y i - y₀ i ∈
        Ideal.span {Matrix.det (Matrix.of fun i j ↦ eval y₀ (pderiv j (F i)))} * a := by
  classical
  let J : Matrix σ σ R := Matrix.of fun i j ↦ eval y₀ (pderiv j (F i))
  let z : σ → MvPolynomial σ R := (Matrix.adjugate J).map C *ᵥ X
  have he (i : σ) : ∃ e ∈ a, Matrix.det J ^ 2 * e = eval y₀ (F i) :=
    Ideal.mem_span_singleton_mul.mp (hF i)
  choose e he hFe using he
  obtain ⟨Q, hQ⟩ := exists_adjugate_scaled_remainder F y₀
  let G : σ → MvPolynomial σ R := fun i ↦ C (e i) + X i + Q i
  have hGzero (i : σ) : eval (0 : σ → R) (G i) ∈ a := by
    simpa only [G, map_add, eval_C, eval_X, Pi.zero_apply,
      eval_zero_eq_zero_of_mem_idealOfVars_sq (hQ i).1, add_zero] using he i
  have hGjac : Matrix.of (fun i j ↦ eval (0 : σ → R) (pderiv j (G i))) =
      (1 : Matrix σ σ R) := by
    ext i j
    exact (eval_zero_pderiv_C_add_X_add e Q (fun i ↦ (hQ i).1) i j).trans
      Matrix.one_apply.symm
  have hGunit : IsUnit (Matrix.det
      (Matrix.of fun i j ↦ eval (0 : σ → R) (pderiv j (G i)))) := by
    rw [hGjac, Matrix.det_one]
    exact isUnit_one
  obtain ⟨u, hu, hua⟩ := exists_eval_eq_zero_mod_ideal_of_isUnit_det
    G (0 : σ → R) a ha hGzero hGunit
  have hua' (i : σ) : u i ∈ a := by simpa using hua i
  let y : σ → R := fun i ↦ y₀ i + Matrix.det J * eval u (z i)
  refine ⟨y, ?_, ?_⟩
  · intro i
    have hpoly : aeval (fun j ↦ C (y₀ j) + C (Matrix.det J) * z j) (F i) =
        C (Matrix.det J ^ 2) * G i := by
      have hQi := (hQ i).2
      change aeval (fun j ↦ C (y₀ j) + C (Matrix.det J) * z j) (F i) =
        C (eval y₀ (F i)) + C (Matrix.det J ^ 2) * (X i + Q i) at hQi
      rw [hQi, ← hFe i, map_mul]
      dsimp only [G]
      ring
    have h := congrArg (aeval u) hpoly
    simpa only [comp_aeval_apply, aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply, map_add, map_mul, aeval_eq_eval, hu i, mul_zero, y] using h
  · intro i
    apply Ideal.mem_span_singleton_mul.mpr
    refine ⟨eval u (z i), ?_, ?_⟩
    · change eval u (∑ j, C (Matrix.adjugate J i j) * X j) ∈ a
      simp only [map_sum, map_mul, eval_C, eval_X]
      exact a.sum_mem fun j _ ↦ a.mul_mem_left _ (hua' j)
    · dsimp only [y]
      ring

end HenselianLocalRing
