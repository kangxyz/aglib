/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

/-!
# Stability of the unit quotient in distinguished factorizations

Mixed maximal-adic precision strictly exceeding the distinguished degree
preserves the first nonzero residue coefficient. Consequently a quotient by
a nearby distinguished polynomial of the same degree is a unit. This supplies
the missing unit comparison, rather than inferring it from divisibility alone.
-/

@[expose] public section

namespace PowerSeries

variable {B : Type*} [CommRing B] [IsLocalRing B]

/-- Mixed maximal-adic precision preserves residue coefficients below that precision. -/
theorem residue_coeff_eq_of_sub_mem_maximalIdeal_pow
    (f g : PowerSeries B) (c d : ℕ) (hd : d < c)
    (h : f - g ∈ IsLocalRing.maximalIdeal (PowerSeries B) ^ c) :
    IsLocalRing.residue B (coeff d f) = IsLocalRing.residue B (coeff d g) := by
  let ρ := map (IsLocalRing.residue B)
  have hm : (IsLocalRing.maximalIdeal (PowerSeries B) ^ c).map ρ ≤
      IsLocalRing.maximalIdeal (PowerSeries (IsLocalRing.ResidueField B)) ^ c := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le ρ) c
  have hmem := hm (Ideal.mem_map_of_mem ρ h)
  rw [maximalIdeal_eq_span_X, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  have hc := X_pow_dvd_iff.mp hmem d hd
  simpa only [ρ, map_sub, coeff_map, sub_eq_zero] using hc

/-- A sufficiently close product with a distinguished divisor of the same degree
has a unit quotient whenever the original factorization has a unit quotient. -/
theorem isUnit_of_distinguished_mul_sub_mem_maximalIdeal_pow
    (P₀ P₁ : Polynomial B)
    (hP₀ : P₀.IsDistinguishedAt (IsLocalRing.maximalIdeal B))
    (hP₁ : P₁.IsDistinguishedAt (IsLocalRing.maximalIdeal B))
    (hdegree : P₁.natDegree = P₀.natDegree)
    (u q : PowerSeries B) (hu : IsUnit u) (c : ℕ) (hc : P₀.natDegree < c)
    (hclose : (P₁ : PowerSeries B) * q - (P₀ : PowerSeries B) * u ∈
      IsLocalRing.maximalIdeal (PowerSeries B) ^ c) : IsUnit q := by
  have hmap₀ : (P₀ : PowerSeries B).map (IsLocalRing.residue B) = X ^ P₀.natDegree := by
    have h : P₀.map (IsLocalRing.residue B) = Polynomial.X ^ P₀.natDegree :=
      hP₀.map_eq_X_pow
    rw [← Polynomial.polynomial_map_coe, h, Polynomial.coe_pow, Polynomial.coe_X]
  have hmap₁ : (P₁ : PowerSeries B).map (IsLocalRing.residue B) = X ^ P₀.natDegree := by
    have h : P₁.map (IsLocalRing.residue B) = Polynomial.X ^ P₁.natDegree :=
      hP₁.map_eq_X_pow
    rw [← Polynomial.polynomial_map_coe, h, Polynomial.coe_pow, Polynomial.coe_X, hdegree]
  have heq := residue_coeff_eq_of_sub_mem_maximalIdeal_pow
    ((P₁ : PowerSeries B) * q) ((P₀ : PowerSeries B) * u) c P₀.natDegree hc hclose
  have hconstant : IsLocalRing.residue B (constantCoeff q) =
      IsLocalRing.residue B (constantCoeff u) := by
    change coeff P₀.natDegree (map (IsLocalRing.residue B) ((P₁ : PowerSeries B) * q)) =
      coeff P₀.natDegree (map (IsLocalRing.residue B) ((P₀ : PowerSeries B) * u)) at heq
    simpa only [map_mul, hmap₁, hmap₀, coeff_X_pow_mul', le_refl, ite_true,
      Nat.sub_self, coeff_map, coeff_zero_eq_constantCoeff] using heq
  apply isUnit_iff_constantCoeff.mpr
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  rw [hconstant]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr (hu.map constantCoeff)

end PowerSeries
