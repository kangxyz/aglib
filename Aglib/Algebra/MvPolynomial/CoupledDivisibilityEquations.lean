/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.MvPolynomial.UniversalDivisibilityEquations

/-!
# Coupled divisibility by a monic polynomial and its square

A single family of `d` coefficients determines `P`; the value remainders have
`2 * d` coefficients. The equations enforce divisibility of one polynomial by
`P` and of the remaining polynomials by that very same `P ^ 2`. There is no
independent degree-`2 * d` divisor. A fixed polynomial quotient approximation
is retained in the reconstructed values, and polynomial division supplies
actual quotient polynomials for subsequent ideal-precision control.
-/

@[expose] public section

namespace MvPolynomial

/-- The single universal monic divisor, with only `d` free coefficients. -/
noncomputable def coupledMonicDivisor (σ R : Type*) [CommRing R] (d : ℕ) :
    Polynomial (MvPolynomial (Fin d ⊕ (σ × Fin (2 * d))) R) :=
  Polynomial.X ^ d + ∑ j : Fin d,
    Polynomial.C (X (Sum.inl j)) * Polynomial.X ^ (j : ℕ)

/-- A reconstructed value using the square of the same divisor and a short remainder. -/
noncomputable def coupledPolynomialValue {σ R : Type*} [CommRing R] (d : ℕ)
    (z : σ → Polynomial R) (i : σ) :
    Polynomial (MvPolynomial (Fin d ⊕ (σ × Fin (2 * d))) R) :=
  coupledMonicDivisor σ R d ^ 2 * (z i).map C +
    ∑ j : Fin (2 * d), Polynomial.C (X (Sum.inr (i, j))) * Polynomial.X ^ (j : ℕ)

/-- Substitution of the reconstructed values into the original polynomial. -/
noncomputable def coupledPolynomialSubstitution {σ R : Type*} [CommRing R] (d : ℕ)
    (z : σ → Polynomial R) (F : MvPolynomial σ (Polynomial R)) :
    Polynomial (MvPolynomial (Fin d ⊕ (σ × Fin (2 * d))) R) :=
  eval₂Hom (Polynomial.mapRingHom C) (coupledPolynomialValue d z) F

/-- A coefficient equation for divisibility by the single universal divisor. -/
noncomputable def coupledDivisibilityEquation {σ R : Type*} [CommRing R] (d : ℕ)
    (z : σ → Polynomial R) (F : MvPolynomial σ (Polynomial R)) (k : Fin d) :
    MvPolynomial (Fin d ⊕ (σ × Fin (2 * d))) R :=
  (coupledPolynomialSubstitution d z F %ₘ coupledMonicDivisor σ R d).coeff k

/-- A coefficient equation for divisibility by the square of that divisor. -/
noncomputable def coupledSquareDivisibilityEquation {σ R : Type*} [CommRing R] (d : ℕ)
    (z : σ → Polynomial R) (F : MvPolynomial σ (Polynomial R)) (k : Fin (2 * d)) :
    MvPolynomial (Fin d ⊕ (σ × Fin (2 * d))) R :=
  (coupledPolynomialSubstitution d z F %ₘ coupledMonicDivisor σ R d ^ 2).coeff k

/-- The actual quotient by the square divisor, not an independent parameter. -/
noncomputable def coupledSquareQuotient {σ R : Type*} [CommRing R] (d : ℕ)
    (z : σ → Polynomial R) (F : MvPolynomial σ (Polynomial R)) :
    Polynomial (MvPolynomial (Fin d ⊕ (σ × Fin (2 * d))) R) :=
  coupledPolynomialSubstitution d z F /ₘ coupledMonicDivisor σ R d ^ 2

variable {σ R S : Type*} [CommRing R] [CommRing S]

lemma coupledMonicDivisor_monic (d : ℕ) : (coupledMonicDivisor σ R d).Monic :=
  Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)

lemma degree_coupledMonicDivisor_le (d : ℕ) :
    (coupledMonicDivisor σ R d).degree ≤ d :=
  (Polynomial.degree_add_le _ _).trans
    (max_le (Polynomial.degree_X_pow_le d) (Polynomial.degree_sum_fin_lt _).le)

lemma degree_coupledMonicDivisor_sq_le (d : ℕ) :
    (coupledMonicDivisor σ R d ^ 2).degree ≤ (2 * d : ℕ) := by
  apply Polynomial.degree_le_of_natDegree_le
  exact Polynomial.natDegree_pow_le_of_le 2
    (Polynomial.natDegree_le_of_degree_le (degree_coupledMonicDivisor_le d))

lemma map_coupledMonicDivisor (d : ℕ) (φ : R →+* S)
    (x : Fin d ⊕ (σ × Fin (2 * d)) → S) :
    (coupledMonicDivisor σ R d).map (eval₂Hom φ x) =
      Polynomial.X ^ d + ∑ j : Fin d,
        Polynomial.C (x (Sum.inl j)) * Polynomial.X ^ (j : ℕ) := by
  simp [coupledMonicDivisor, Polynomial.map_sum]

lemma map_coupledPolynomialValue (d : ℕ) (z : σ → Polynomial R) (φ : R →+* S)
    (x : Fin d ⊕ (σ × Fin (2 * d)) → S) (i : σ) :
    (coupledPolynomialValue d z i).map (eval₂Hom φ x) =
      (Polynomial.X ^ d + ∑ j : Fin d,
        Polynomial.C (x (Sum.inl j)) * Polynomial.X ^ (j : ℕ)) ^ 2 * (z i).map φ +
      ∑ j : Fin (2 * d), Polynomial.C (x (Sum.inr (i, j))) * Polynomial.X ^ (j : ℕ) := by
  have hC : (eval₂Hom φ x).comp C = φ := by ext r; simp
  simp [coupledPolynomialValue, Polynomial.map_sum, Polynomial.map_map,
    map_coupledMonicDivisor, hC]

/-- The specialization of the reconstructed value polynomial, retaining the fixed quotient. -/
theorem map_coupledPolynomialSubstitution (d : ℕ) (z : σ → Polynomial R)
    (φ : R →+* S) (x : Fin d ⊕ (σ × Fin (2 * d)) → S)
    (F : MvPolynomial σ (Polynomial R)) :
    (coupledPolynomialSubstitution d z F).map (eval₂Hom φ x) =
      eval₂Hom (Polynomial.mapRingHom φ)
        (fun i ↦ (Polynomial.X ^ d + ∑ j : Fin d,
          Polynomial.C (x (Sum.inl j)) * Polynomial.X ^ (j : ℕ)) ^ 2 * (z i).map φ +
          ∑ j : Fin (2 * d), Polynomial.C (x (Sum.inr (i, j))) * Polynomial.X ^ (j : ℕ)) F := by
  change Polynomial.mapRingHom (eval₂Hom φ x)
    (eval₂Hom (Polynomial.mapRingHom C) (coupledPolynomialValue d z) F) = _
  rw [map_eval₂Hom, Polynomial.mapRingHom_comp]
  have hC : (eval₂Hom φ x).comp C = φ := by ext r; simp
  rw [hC]
  have hvalues : (fun i ↦ Polynomial.mapRingHom (eval₂Hom φ x)
      (coupledPolynomialValue d z i)) =
      (fun i ↦ (Polynomial.X ^ d + ∑ j : Fin d,
        Polynomial.C (x (Sum.inl j)) * Polynomial.X ^ (j : ℕ)) ^ 2 * (z i).map φ +
        ∑ j : Fin (2 * d), Polynomial.C (x (Sum.inr (i, j))) * Polynomial.X ^ (j : ℕ)) := by
    funext i
    exact map_coupledPolynomialValue d z φ x i
  rw [hvalues]

/-- The finite system couples `P ∣ g(Y)` and `P ^ 2 ∣ Fᵢ(Y)` using one actual `P`. -/
theorem coupledDivisibilitySystem_iff {ι : Type*} (d : ℕ) (z : σ → Polynomial R)
    (φ : R →+* S) (x : Fin d ⊕ (σ × Fin (2 * d)) → S)
    (g : MvPolynomial σ (Polynomial R)) (F : ι → MvPolynomial σ (Polynomial R)) :
    ((∀ k, eval₂Hom φ x (coupledDivisibilityEquation d z g k) = 0) ∧
      ∀ q : ι × Fin (2 * d),
        eval₂Hom φ x (coupledSquareDivisibilityEquation d z (F q.1) q.2) = 0) ↔
      ((coupledMonicDivisor σ R d).map (eval₂Hom φ x) ∣
        (coupledPolynomialSubstitution d z g).map (eval₂Hom φ x)) ∧
      ∀ i, (coupledMonicDivisor σ R d).map (eval₂Hom φ x) ^ 2 ∣
        (coupledPolynomialSubstitution d z (F i)).map (eval₂Hom φ x) := by
  have hg := Polynomial.map_dvd_iff_fin_coeff_modByMonic_eq_zero (eval₂Hom φ x)
    (coupledPolynomialSubstitution d z g) (coupledMonicDivisor σ R d)
    (coupledMonicDivisor_monic d) d (degree_coupledMonicDivisor_le d)
  have hf (i : ι) := Polynomial.map_dvd_iff_fin_coeff_modByMonic_eq_zero (eval₂Hom φ x)
    (coupledPolynomialSubstitution d z (F i)) (coupledMonicDivisor σ R d ^ 2)
    ((coupledMonicDivisor_monic d).pow 2) (2 * d) (degree_coupledMonicDivisor_sq_le d)
  simp only [Polynomial.map_pow] at hf
  simp only [coupledDivisibilityEquation, coupledSquareDivisibilityEquation, Prod.forall,
    ← hg, ← hf]

/-- Vanishing square-remainder equations give the actual specialized quotient identity. -/
theorem eq_sq_mul_map_coupledSquareQuotient (d : ℕ) (z : σ → Polynomial R)
    (φ : R →+* S) (x : Fin d ⊕ (σ × Fin (2 * d)) → S)
    (F : MvPolynomial σ (Polynomial R))
    (hF : ∀ k, eval₂Hom φ x (coupledSquareDivisibilityEquation d z F k) = 0) :
    (coupledPolynomialSubstitution d z F).map (eval₂Hom φ x) =
      (coupledMonicDivisor σ R d).map (eval₂Hom φ x) ^ 2 *
        (coupledSquareQuotient d z F).map (eval₂Hom φ x) := by
  have hrem : (coupledPolynomialSubstitution d z F %ₘ
      coupledMonicDivisor σ R d ^ 2).map (eval₂Hom φ x) = 0 := by
    rw [Polynomial.map_modByMonic _ ((coupledMonicDivisor_monic d).pow 2),
      Polynomial.modByMonic_eq_zero_iff_dvd (((coupledMonicDivisor_monic d).pow 2).map _)]
    exact (Polynomial.map_dvd_iff_fin_coeff_modByMonic_eq_zero (eval₂Hom φ x)
      (coupledPolynomialSubstitution d z F) (coupledMonicDivisor σ R d ^ 2)
      ((coupledMonicDivisor_monic d).pow 2) (2 * d)
      (degree_coupledMonicDivisor_sq_le d)).mpr hF
  have h := congrArg (Polynomial.map (eval₂Hom φ x))
    (Polynomial.modByMonic_add_div (coupledPolynomialSubstitution d z F)
      (coupledMonicDivisor σ R d ^ 2))
  simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    hrem, zero_add, coupledSquareQuotient] using h.symm

end MvPolynomial
