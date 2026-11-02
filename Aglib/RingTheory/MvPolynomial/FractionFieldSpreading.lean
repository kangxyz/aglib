/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPolynomial.AbsoluteIrreducibilitySpecialization
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Localization.Integer

/-! # Spreading an actual fraction-field polynomial

Clearing denominators preserves an explicit scalar-multiple equation for the
original polynomial. Absolute irreducibility survives this nonzero scalar
multiple. The final principal scalar also inverts that same denominator.
No Noetherianity or perfectness assumption is used.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace MvPolynomial

/-- Clear the coefficients of the original fraction-field polynomial by one
nonzero scalar, retaining the exact original polynomial equation. -/
theorem exists_nonzero_scalar_multiple_eq_map
    {σ R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (P : MvPolynomial σ K) :
    ∃ r : R, r ≠ 0 ∧ ∃ Q : MvPolynomial σ R,
      map (algebraMap R K) Q = C (algebraMap R K r) * P := by
  let := algebraMvPolynomial (σ := σ) (R := R) (S := K)
  obtain ⟨⟨_, r, hr, rfl⟩, Q, hQ⟩ :=
    IsLocalization.exists_integer_multiple ((nonZeroDivisors R).map (C (σ := σ))) P
  refine ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr, Q, ?_⟩
  simpa only [Algebra.smul_def, algebraMap_def, map_C] using hQ

/-- The same coefficient-cleared polynomial is absolutely irreducible; its
original denominator and scalar-multiple equation are preserved. -/
theorem exists_cleared_irreducible_map
    {σ R K Ω : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field Ω] [Algebra K Ω] [Algebra R Ω]
    [IsScalarTower R K Ω] (P : MvPolynomial σ K)
    (hP : Irreducible (map (algebraMap K Ω) P)) :
    ∃ r : R, r ≠ 0 ∧ ∃ Q : MvPolynomial σ R,
      map (algebraMap R K) Q = C (algebraMap R K r) * P ∧
      Irreducible (map (algebraMap R Ω) Q) := by
  obtain ⟨r, hr, Q, hQ⟩ := exists_nonzero_scalar_multiple_eq_map (R := R) P
  have hrK : algebraMap R K r ≠ 0 := by
    intro h
    exact hr (IsFractionRing.injective R K (h.trans (map_zero _).symm))
  have hrΩ : algebraMap R Ω r ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R K Ω]
    intro h
    exact hrK ((algebraMap K Ω).injective (h.trans (map_zero _).symm))
  have hQΩ : map (algebraMap R Ω) Q =
      C (algebraMap R Ω r) * map (algebraMap K Ω) P := by
    have h := congrArg (map (algebraMap K Ω)) hQ
    simpa only [map_map, ← IsScalarTower.algebraMap_eq R K Ω,
      map_mul, map_C, ← IsScalarTower.algebraMap_apply R K Ω] using h
  refine ⟨r, hr, Q, hQ, ?_⟩
  rw [hQΩ]
  exact (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr hrΩ).map C)).mpr hP

/-- One original principal base open both inverts the coefficient denominator
and makes every field specialization of the same cleared polynomial
irreducible. The scalar-multiple equation is not replaced by an abstract
hypersurface isomorphism. -/
theorem exists_cleared_forall_irreducible_map
    {σ R K Ω : Type*} [Finite σ] [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω] [IsAlgClosed Ω]
    (P : MvPolynomial σ K) (hP : Irreducible (map (algebraMap K Ω) P)) :
    ∃ r : R, r ≠ 0 ∧ ∃ Q : MvPolynomial σ R,
      map (algebraMap R K) Q = C (algebraMap R K r) * P ∧
      ∃ s : R, s ≠ 0 ∧ r ∣ s ∧
        ∀ (L : Type*) [Field L] (φ : R →+* L), φ s ≠ 0 → Irreducible (map φ Q) := by
  obtain ⟨r, hr, Q, hQ, hQΩ⟩ := exists_cleared_irreducible_map (R := R) P hP
  obtain ⟨s, hs, h⟩ :=
    FactorizationAlgebra.exists_ne_zero_forall_irreducible_map R K Ω Q hQΩ
  refine ⟨r, hr, Q, hQ, r * s, mul_ne_zero hr hs, dvd_mul_right r s, ?_⟩
  intro L _ φ hφ
  apply h L φ
  intro hz
  apply hφ
  rw [map_mul, hz, mul_zero]

end MvPolynomial
