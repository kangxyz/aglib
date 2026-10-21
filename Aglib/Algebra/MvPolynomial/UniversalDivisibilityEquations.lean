/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.MonicRemainderEquations
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Universal finite equations for monic divisibility

The parameters are the `d` lower coefficients of a monic polynomial and the
`d` coefficients of each substituted unknown. Taking the first `d` remainder
coefficients produces actual multivariate polynomials in these parameters.
Their vanishing after any specialization is equivalent to the specialized
monic polynomial dividing the specialized original equation. For a finite
family of equations and finitely many unknowns this is a finite polynomial
system over the original coefficient ring.
-/

@[expose] public section

namespace MvPolynomial

/-- The universal monic polynomial of degree bounded by `d`. -/
noncomputable def universalMonicDivisor (σ : Type*) (R : Type*) [CommRing R] (d : ℕ) :
    Polynomial (MvPolynomial (Fin d ⊕ (σ × Fin d)) R) :=
  Polynomial.X ^ d + ∑ j : Fin d,
    Polynomial.C (X (Sum.inl j)) * Polynomial.X ^ (j : ℕ)

/-- The universal polynomial value of an unknown, of degree strictly below `d`. -/
noncomputable def universalRemainderValue {σ R : Type*} [CommRing R] (d : ℕ) (i : σ) :
    Polynomial (MvPolynomial (Fin d ⊕ (σ × Fin d)) R) :=
  ∑ j : Fin d, Polynomial.C (X (Sum.inr (i, j))) * Polynomial.X ^ (j : ℕ)

/-- Substitute the universal bounded-degree values into an actual equation. -/
noncomputable def universalPolynomialSubstitution {σ R : Type*} [CommRing R] (d : ℕ)
    (F : MvPolynomial σ (Polynomial R)) :
    Polynomial (MvPolynomial (Fin d ⊕ (σ × Fin d)) R) :=
  eval₂Hom (Polynomial.mapRingHom C) (universalRemainderValue d) F

/-- One actual polynomial equation expressing a remainder coefficient. -/
noncomputable def universalDivisibilityEquation {σ R : Type*} [CommRing R] (d : ℕ)
    (F : MvPolynomial σ (Polynomial R)) (k : Fin d) :
    MvPolynomial (Fin d ⊕ (σ × Fin d)) R :=
  (universalPolynomialSubstitution d F %ₘ universalMonicDivisor σ R d).coeff k

variable {σ R S : Type*} [CommRing R] [CommRing S]

lemma universalMonicDivisor_monic (d : ℕ) : (universalMonicDivisor σ R d).Monic :=
  Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)

lemma degree_universalMonicDivisor_le (d : ℕ) :
    (universalMonicDivisor σ R d).degree ≤ d := by
  apply (Polynomial.degree_add_le _ _).trans
  exact max_le (Polynomial.degree_X_pow_le d) (Polynomial.degree_sum_fin_lt _).le

lemma map_universalMonicDivisor (d : ℕ) (φ : R →+* S)
    (x : Fin d ⊕ (σ × Fin d) → S) :
    (universalMonicDivisor σ R d).map (eval₂Hom φ x) =
      Polynomial.X ^ d + ∑ j : Fin d,
        Polynomial.C (x (Sum.inl j)) * Polynomial.X ^ (j : ℕ) := by
  simp [universalMonicDivisor, Polynomial.map_sum]

lemma map_universalRemainderValue (d : ℕ) (φ : R →+* S)
    (x : Fin d ⊕ (σ × Fin d) → S) (i : σ) :
    (universalRemainderValue (R := R) d i).map (eval₂Hom φ x) =
      ∑ j : Fin d, Polynomial.C (x (Sum.inr (i, j))) * Polynomial.X ^ (j : ℕ) := by
  simp [universalRemainderValue, Polynomial.map_sum]

lemma map_universalPolynomialSubstitution (d : ℕ) (φ : R →+* S)
    (x : Fin d ⊕ (σ × Fin d) → S) (F : MvPolynomial σ (Polynomial R)) :
    (universalPolynomialSubstitution d F).map (eval₂Hom φ x) =
      eval₂Hom (Polynomial.mapRingHom φ)
        (fun i ↦ ∑ j : Fin d,
          Polynomial.C (x (Sum.inr (i, j))) * Polynomial.X ^ (j : ℕ)) F := by
  change Polynomial.mapRingHom (eval₂Hom φ x)
    (eval₂Hom (Polynomial.mapRingHom C) (universalRemainderValue d) F) = _
  rw [map_eval₂Hom, Polynomial.mapRingHom_comp]
  have hC : (eval₂Hom φ x).comp C = φ := by
    ext r
    simp
  rw [hC]
  have hvalues : (fun i ↦ Polynomial.mapRingHom (eval₂Hom φ x)
      (universalRemainderValue (R := R) d i)) =
      (fun i ↦ ∑ j : Fin d,
        Polynomial.C (x (Sum.inr (i, j))) * Polynomial.X ^ (j : ℕ)) := by
    funext i
    exact map_universalRemainderValue d φ x i
  rw [hvalues]

/-- Specializing the actual remainder equations is equivalent to actual monic divisibility. -/
theorem universalDivisibilityEquations_iff (d : ℕ) (φ : R →+* S)
    (x : Fin d ⊕ (σ × Fin d) → S) (F : MvPolynomial σ (Polynomial R)) :
    (∀ k : Fin d, eval₂Hom φ x (universalDivisibilityEquation d F k) = 0) ↔
      (Polynomial.X ^ d + ∑ j : Fin d,
        Polynomial.C (x (Sum.inl j)) * Polynomial.X ^ (j : ℕ)) ∣
      eval₂Hom (Polynomial.mapRingHom φ)
        (fun i ↦ ∑ j : Fin d,
          Polynomial.C (x (Sum.inr (i, j))) * Polynomial.X ^ (j : ℕ)) F := by
  have h := Polynomial.map_dvd_iff_fin_coeff_modByMonic_eq_zero
    (eval₂Hom φ x) (universalPolynomialSubstitution d F)
    (universalMonicDivisor σ R d) (universalMonicDivisor_monic d) d
    (degree_universalMonicDivisor_le d)
  rw [map_universalMonicDivisor, map_universalPolynomialSubstitution] at h
  exact h.symm

/-- The same construction simultaneously encodes an arbitrary family of equations.
If `ι` and `σ` are finite, both its equation and parameter types are finite. -/
theorem universalDivisibilitySystem_iff {ι : Type*} (d : ℕ) (φ : R →+* S)
    (x : Fin d ⊕ (σ × Fin d) → S) (F : ι → MvPolynomial σ (Polynomial R)) :
    (∀ z : ι × Fin d, eval₂Hom φ x (universalDivisibilityEquation d (F z.1) z.2) = 0) ↔
      ∀ i, (Polynomial.X ^ d + ∑ j : Fin d,
        Polynomial.C (x (Sum.inl j)) * Polynomial.X ^ (j : ℕ)) ∣
      eval₂Hom (Polynomial.mapRingHom φ)
        (fun s ↦ ∑ j : Fin d,
          Polynomial.C (x (Sum.inr (s, j))) * Polynomial.X ^ (j : ℕ)) (F i) := by
  simp only [Prod.forall, universalDivisibilityEquations_iff]

end MvPolynomial
