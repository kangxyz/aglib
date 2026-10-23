/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.Brauer.MatrixNormInvariance
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Finite Galois coefficient descent for an actual determinant polynomial

Galois invariance of the constructed matrix norm polynomial descends its
coefficients uniquely. The descended polynomial is nonzero and homogeneous of
the matrix size. Invariance is an explicit intermediate hypothesis: this leaf
does not assert that every central simple algebra has a separable splitting.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace Algebra

variable {K L A : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [Ring A] [Algebra L A] {m n : ℕ}

private theorem exists_polynomial_of_fixed_coefficients
    (p : MvPolynomial (Fin m) L)
    (hp : ∀ s : L ≃ₐ[K] L, map s.toRingHom p = p) :
    ∃ q : MvPolynomial (Fin m) K, map (algebraMap K L) q = p := by
  apply mem_range_map_iff_coeffs_subset.mpr
  intro c hc
  obtain ⟨d, _, rfl⟩ := mem_coeffs_iff.mp hc
  apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
  intro s
  have h := congrArg (fun q : MvPolynomial (Fin m) L => q.coeff d) (hp s)
  rw [coeff_map] at h
  change s (p.coeff d) = p.coeff d at h
  exact h

/-- Finite Galois invariance descends the actual determinant polynomial,
retaining its degree and its nonvanishing as a polynomial. -/
theorem exists_matrixNormPolynomial_descent
    (b : Module.Basis (Fin m) L A)
    (f : A →ₐ[L] Matrix (Fin n) (Fin n) L)
    (hfixed : ∀ s : L ≃ₐ[K] L,
      map s.toRingHom (matrixNormPolynomial b f) = matrixNormPolynomial b f) :
    ∃ p : MvPolynomial (Fin m) K,
      map (algebraMap K L) p = matrixNormPolynomial b f ∧
      p.IsHomogeneous n ∧ p ≠ 0 := by
  obtain ⟨p, hp⟩ := exists_polynomial_of_fixed_coefficients (matrixNormPolynomial b f) hfixed
  refine ⟨p, hp, ?_, ?_⟩
  · apply IsHomogeneous.of_map (FaithfulSMul.algebraMap_injective K L)
    rw [hp]
    exact matrixNormPolynomial_isHomogeneous b f
  · intro hz
    exact matrixNormPolynomial_ne_zero b f (hp.symm.trans (by simp [hz]))

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The descended polynomial is unique for the original coefficient embedding. -/
theorem matrixNormPolynomial_descent_unique
    (b : Module.Basis (Fin m) L A)
    (f : A →ₐ[L] Matrix (Fin n) (Fin n) L)
    {p q : MvPolynomial (Fin m) K}
    (hp : map (algebraMap K L) p = matrixNormPolynomial b f)
    (hq : map (algebraMap K L) q = matrixNormPolynomial b f) : p = q :=
  map_injective _ (FaithfulSMul.algebraMap_injective K L) (hp.trans hq.symm)

end Algebra
