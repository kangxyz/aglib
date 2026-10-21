/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Actual triangular polynomial coordinate changes

Adding powers of a fixed pivot to the other variables is an actual polynomial
algebra automorphism, with subtraction as its inverse. Invertibility does not
require positive exponents. Positivity away from the pivot is used only to
preserve constant coefficients, hence the origin over any local coefficient ring.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

variable (R : Type*) [CommRing R] {σ : Type*} [DecidableEq σ]

/-- The actual polynomial automorphism adding pivot powers away from the pivot. -/
def triangularAlgEquiv (p : σ) (e : σ → ℕ) : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R := by
  let a : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
    aeval (fun i => if i = p then X p else X i + X p ^ e i)
  let b : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
    aeval (fun i => if i = p then X p else X i - X p ^ e i)
  refine AlgEquiv.ofAlgHom a b ?_ ?_
  · apply algHom_ext
    intro i
    change a (b (X i)) = X i
    by_cases hi : i = p
    · subst i
      simp [a, b]
    · simp [a, b, hi]
  · apply algHom_ext
    intro i
    change b (a (X i)) = X i
    by_cases hi : i = p
    · subst i
      simp [a, b]
    · simp [a, b, hi]

/-- The forward polynomial coordinate formula. -/
@[simp] theorem triangularAlgEquiv_X (p : σ) (e : σ → ℕ) (i : σ) :
    triangularAlgEquiv R p e (X i) = if i = p then X p else X i + X p ^ e i := by
  exact aeval_X _ _

/-- The inverse polynomial coordinate formula. -/
@[simp] theorem triangularAlgEquiv_symm_X (p : σ) (e : σ → ℕ) (i : σ) :
    (triangularAlgEquiv R p e).symm (X i) = if i = p then X p else X i - X p ^ e i := by
  exact aeval_X _ _

/-- Positive off-pivot exponents preserve the actual constant coefficient. -/
theorem constantCoeff_triangularAlgEquiv (p : σ) (e : σ → ℕ)
    (he : ∀ i, i ≠ p → 0 < e i) (f : MvPolynomial σ R) :
    constantCoeff (triangularAlgEquiv R p e f) = constantCoeff f := by
  have hX (i : σ) : constantCoeff (triangularAlgEquiv R p e (X i)) = 0 := by
    rw [triangularAlgEquiv_X]
    split_ifs with hi
    · exact constantCoeff_X (R := R) p
    · simp only [map_add, map_pow, constantCoeff_X, zero_pow (he i hi).ne', add_zero]
  induction f using MvPolynomial.induction_on with
  | C r =>
      have h : triangularAlgEquiv R p e (C r) = C r :=
        (triangularAlgEquiv R p e).commutes r
      rw [h]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i _ => simp only [map_mul, hX, constantCoeff_X, mul_zero]

/-- The inverse also preserves constant coefficients; this follows from the actual inverse law. -/
theorem constantCoeff_triangularAlgEquiv_symm (p : σ) (e : σ → ℕ)
    (he : ∀ i, i ≠ p → 0 < e i) (f : MvPolynomial σ R) :
    constantCoeff ((triangularAlgEquiv R p e).symm f) = constantCoeff f := by
  have h := constantCoeff_triangularAlgEquiv R p e he ((triangularAlgEquiv R p e).symm f)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

end MvPolynomial
