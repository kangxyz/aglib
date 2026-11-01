/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Basic

/-!
# Reparametrization and leading coefficients of Hilbert polynomials

Tensoring a coherent module on projective space by `O(a)` translates its
native Hilbert polynomial and preserves its leading coefficient. Replacing
an integer parameter `m` by `c * m` composes the unique rational polynomial
with `C c * X`; for nonzero `c` this multiplies its leading coefficient by
`c ^ natDegree`.

The cancellation lemma isolates the numerical conclusion of a degree
argument. Its leading-coefficient hypothesis is explicit: this file does
not supply finite-map rank scaling or identify polynomial degree with
support dimension. In particular it asserts no equality of whole Euler
characteristics under a finite flat morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped Polynomial

namespace Polynomial

/-- Integer dilation preserves polynomiality at every integer. -/
theorem IsPolynomialOnInt.comp_mul {f : ℤ → ℤ} (hf : IsPolynomialOnInt f) (c : ℤ) :
    IsPolynomialOnInt fun m => f (c * m) := by
  obtain ⟨P, hP⟩ := hf
  refine ⟨P.comp (C (c : ℚ) * X), fun m => ?_⟩
  rw [hP, eval_comp, eval_mul, eval_C, eval_X, Int.cast_mul]

/-- The chosen polynomial of an integer dilation is the original polynomial
composed with the same scalar multiplication. This includes `c = 0`. -/
theorem polynomialOnInt_comp_mul {f : ℤ → ℤ} (hf : IsPolynomialOnInt f) (c : ℤ) :
    polynomialOnInt (fun m => f (c * m)) = (polynomialOnInt f).comp (C (c : ℚ) * X) := by
  apply IsPolynomialOnInt.polynomialOnInt_eq
  intro m
  rw [hf.eval_polynomialOnInt, eval_comp, eval_mul, eval_C, eval_X, Int.cast_mul]

/-- Dilation scales the leading coefficient by the parameter to the actual
polynomial degree, including degree zero. -/
theorem leadingCoeff_comp_C_mul_X (P : ℚ[X]) {c : ℚ} (hc : c ≠ 0) :
    (P.comp (C c * X)).leadingCoeff = P.leadingCoeff * c ^ P.natDegree := by
  rw [leadingCoeff_comp (by rw [natDegree_C_mul_X c hc]; exact one_ne_zero),
    leadingCoeff_C_mul_X]

/-- A nonzero leading term determines the scalar in a dilation law. This
uses only leading coefficients, not equality of the two whole polynomials. -/
theorem eq_pow_of_leadingCoeff_comp_C_mul_X {P : ℚ[X]} (hP : P ≠ 0)
    {c r : ℚ} (hc : c ≠ 0)
    (h : (P.comp (C c * X)).leadingCoeff = r * P.leadingCoeff) :
    r = c ^ P.natDegree := by
  rw [leadingCoeff_comp_C_mul_X P hc, mul_comm r P.leadingCoeff] at h
  exact (mul_left_cancel₀ (leadingCoeff_ne_zero.mpr hP) h).symm

/-- The natural-number degree extracted from a nonzero Hilbert leading
term. A geometric comparison must supply the displayed leading-coefficient
law and the actual polynomial degree separately. -/
theorem nat_eq_pow_of_leadingCoeff_comp_C_mul_X {P : ℚ[X]} (hP : P ≠ 0)
    (c r d : ℕ) (hc : 0 < c) (hd : P.natDegree = d)
    (h : (P.comp (C (c : ℚ) * X)).leadingCoeff = (r : ℚ) * P.leadingCoeff) :
    r = c ^ d := by
  have hcast : (c : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hc)
  have heq := eq_pow_of_leadingCoeff_comp_C_mul_X hP hcast h
  rw [hd] at heq
  exact_mod_cast heq

end Polynomial

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (k : Type u) [Field k] (ι : Type u)

/-- The original tensor-twist composition translates the Hilbert function.
No coherence or dimension hypothesis is needed for this identity. -/
theorem projectiveHilbertFunction_twistingTensor
    (F : (ProjectiveSpace k ι).Modules) (a m : ℤ) :
    projectiveHilbertFunction k ι
      ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι a)).obj F) m =
        projectiveHilbertFunction k ι F (m + a) :=
  projectiveEulerChar_congr k ι ((twistingTensorCompIso k ι m a).app F)

/-- Tensoring a coherent module by `O(a)` translates its native Hilbert
polynomial by `a`, through the original tensor comparison. -/
theorem projectiveHilbertPolynomial_twistingTensor (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace k ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) (a : ℤ) :
    projectiveHilbertPolynomial k ι
      ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι a)).obj F) =
        (projectiveHilbertPolynomial k ι F).comp (Polynomial.X + Polynomial.C (a : ℚ)) := by
  apply projectiveHilbertPolynomial_eq_of_eval
  intro m
  rw [projectiveHilbertFunction_twistingTensor,
    projectiveHilbertFunction_eq_eval k ι n e F hF,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Int.cast_add]

/-- Tensoring by `O(a)` preserves the leading coefficient of the original
Hilbert polynomial, including when the module is zero. -/
theorem leadingCoeff_projectiveHilbertPolynomial_twistingTensor
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace k ι).Modules)
    (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) (a : ℤ) :
    (projectiveHilbertPolynomial k ι
      ((moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι a)).obj F)).leadingCoeff =
        (projectiveHilbertPolynomial k ι F).leadingCoeff := by
  rw [projectiveHilbertPolynomial_twistingTensor k ι n e F hF a,
    Polynomial.leadingCoeff_comp (by
      rw [Polynomial.natDegree_X_add_C]; exact one_ne_zero),
    Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]

end AlgebraicGeometry.Scheme.Cohomology
