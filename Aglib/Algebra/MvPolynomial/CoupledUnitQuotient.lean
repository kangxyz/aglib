/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.MvPolynomial.CoupledDivisibilityEquations
public import Aglib.RingTheory.PowerSeries.DistinguishedUnitQuotient

/-!
# The actual coupled divisor has a unit quotient

Parameter congruence preserves the distinguished divisor. A reconstructed point
close to the original formal point preserves the leading residue coefficient
of the Jacobian minor. The quotient obtained by native monic polynomial
division is therefore a unit in the formal ring, rather than merely a divisor.
-/

@[expose] public section

namespace MvPolynomial

variable {A B σ : Type*} [CommRing A] [CommRing B] [IsLocalRing B]

lemma natDegree_map_coupledMonicDivisor (d : ℕ) (φ : A →+* B)
    (x : Fin d ⊕ (σ × Fin (2 * d)) → B) :
    ((coupledMonicDivisor σ A d).map (eval₂Hom φ x)).natDegree = d := by
  rw [map_coupledMonicDivisor, Polynomial.natDegree_add_eq_left_of_degree_lt,
    Polynomial.natDegree_X_pow]
  simpa only [Polynomial.degree_X_pow] using
    Polynomial.degree_sum_fin_lt (fun j : Fin d ↦ x (Sum.inl j))

/-- Congruent parameters give another distinguished polynomial of the same degree. -/
theorem isDistinguishedAt_map_coupledMonicDivisor
    (d : ℕ) (φ : A →+* B) (x₀ x₁ : Fin d ⊕ (σ × Fin (2 * d)) → B)
    (hP : ((coupledMonicDivisor σ A d).map (eval₂Hom φ x₀)).IsDistinguishedAt
      (IsLocalRing.maximalIdeal B))
    (hx : ∀ k, x₁ k - x₀ k ∈ IsLocalRing.maximalIdeal B) :
    ((coupledMonicDivisor σ A d).map (eval₂Hom φ x₁)).IsDistinguishedAt
      (IsLocalRing.maximalIdeal B) := by
  have he : (IsLocalRing.residue B).comp (eval₂Hom φ x₁) =
      (IsLocalRing.residue B).comp (eval₂Hom φ x₀) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro k
      simp only [RingHom.comp_apply, eval₂Hom_X']
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hx k)
  have hres : ((coupledMonicDivisor σ A d).map (eval₂Hom φ x₁)).map
      (IsLocalRing.residue B) = Polynomial.X ^ d := by
    rw [Polynomial.map_map, he, ← Polynomial.map_map]
    have h : ((coupledMonicDivisor σ A d).map (eval₂Hom φ x₀)).map
        (IsLocalRing.residue B) = Polynomial.X ^
          ((coupledMonicDivisor σ A d).map (eval₂Hom φ x₀)).natDegree := hP.map_eq_X_pow
    rw [h, natDegree_map_coupledMonicDivisor]
  refine ⟨⟨?_⟩, (coupledMonicDivisor_monic d).map _⟩
  intro j hj
  rw [natDegree_map_coupledMonicDivisor] at hj
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change IsLocalRing.residue B
    (((coupledMonicDivisor σ A d).map (eval₂Hom φ x₁)).coeff j) = 0
  have hcoeff := congrArg (fun p : Polynomial (IsLocalRing.ResidueField B) ↦ p.coeff j) hres
  simpa only [Polynomial.coeff_map, Polynomial.coeff_X_pow, ne_of_lt hj, ite_false] using hcoeff

/-- The actual quotient of the reconstructed minor by the coupled monic divisor
is a unit when the formal point and parameters retain sufficient precision. -/
theorem isUnit_map_coupled_divByMonic_of_formal_factorization
    (d : ℕ) (z : σ → Polynomial A) (φ : A →+* B)
    (x₀ x₁ : Fin d ⊕ (σ × Fin (2 * d)) → B)
    (g : MvPolynomial σ (Polynomial A)) (y : σ → PowerSeries B)
    (u : PowerSeries B) (hu : IsUnit u)
    (hP : ((coupledMonicDivisor σ A d).map (eval₂Hom φ x₀)).IsDistinguishedAt
      (IsLocalRing.maximalIdeal B))
    (hg : eval₂Hom
      (Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom φ)) y g =
      ((coupledMonicDivisor σ A d).map (eval₂Hom φ x₀) : PowerSeries B) * u)
    (c : ℕ) (hc : d < c)
    (hx : ∀ k, x₁ k - x₀ k ∈ IsLocalRing.maximalIdeal B)
    (hy : ∀ s, ((coupledPolynomialValue d z s).map (eval₂Hom φ x₁) : PowerSeries B) - y s ∈
      IsLocalRing.maximalIdeal (PowerSeries B) ^ c)
    (heq : ∀ k, eval₂Hom φ x₁ (coupledDivisibilityEquation d z g k) = 0) :
    IsUnit (((coupledPolynomialSubstitution d z g /ₘ coupledMonicDivisor σ A d).map
      (eval₂Hom φ x₁) : Polynomial B) : PowerSeries B) := by
  let P₀ := (coupledMonicDivisor σ A d).map (eval₂Hom φ x₀)
  let P₁ := (coupledMonicDivisor σ A d).map (eval₂Hom φ x₁)
  let H := (coupledPolynomialSubstitution d z g).map (eval₂Hom φ x₁)
  let q := (coupledPolynomialSubstitution d z g /ₘ coupledMonicDivisor σ A d).map
    (eval₂Hom φ x₁)
  have hdvd : P₁ ∣ H :=
    (Polynomial.map_dvd_iff_fin_coeff_modByMonic_eq_zero (eval₂Hom φ x₁)
      (coupledPolynomialSubstitution d z g) (coupledMonicDivisor σ A d)
      (coupledMonicDivisor_monic d) d (degree_coupledMonicDivisor_le d)).mpr heq
  have hrem : H %ₘ P₁ = 0 :=
    (Polynomial.modByMonic_eq_zero_iff_dvd ((coupledMonicDivisor_monic d).map _)).mpr hdvd
  have hproduct : P₁ * q = H := by
    have h := Polynomial.modByMonic_add_div H P₁
    rw [hrem, zero_add] at h
    simpa only [q, Polynomial.map_divByMonic _ (coupledMonicDivisor_monic d)] using h
  let a := IsLocalRing.maximalIdeal (PowerSeries B) ^ c
  let π := Ideal.Quotient.mk a
  have hpoint : (fun s ↦ π ((coupledPolynomialValue d z s).map (eval₂Hom φ x₁) : PowerSeries B)) =
      (fun s ↦ π (y s)) := by
    funext s
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hy s)
  have hsub : H = eval₂Hom (Polynomial.mapRingHom φ)
      (fun s ↦ (coupledPolynomialValue d z s).map (eval₂Hom φ x₁)) g := by
    change Polynomial.mapRingHom (eval₂Hom φ x₁)
      (eval₂Hom (Polynomial.mapRingHom C) (coupledPolynomialValue d z) g) = _
    rw [map_eval₂Hom, Polynomial.mapRingHom_comp]
    have hC : (eval₂Hom φ x₁).comp C = φ := by ext b; simp
    rw [hC]
    simp only [Polynomial.coe_mapRingHom]
  have hcoe : (H : PowerSeries B) = eval₂Hom
      (Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom φ))
      (fun s ↦ ((coupledPolynomialValue d z s).map (eval₂Hom φ x₁) : PowerSeries B)) g := by
    rw [hsub]
    exact map_eval₂Hom (Polynomial.mapRingHom φ) _ Polynomial.coeToPowerSeries.ringHom g
  have hdiff : (H : PowerSeries B) - (P₀ : PowerSeries B) * u ∈ a := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    change π (H : PowerSeries B) = π ((P₀ : PowerSeries B) * u)
    rw [hcoe, map_eval₂Hom, hpoint, ← map_eval₂Hom, hg]
  have hdegree : P₁.natDegree = P₀.natDegree := by
    rw [natDegree_map_coupledMonicDivisor, natDegree_map_coupledMonicDivisor]
  have hprecision : P₀.natDegree < c := by
    simpa only [P₀, natDegree_map_coupledMonicDivisor] using hc
  have hproductclose : (P₁ : PowerSeries B) * (q : PowerSeries B) -
      (P₀ : PowerSeries B) * u ∈ IsLocalRing.maximalIdeal (PowerSeries B) ^ c := by
    simpa only [← Polynomial.coe_mul, hproduct] using hdiff
  exact PowerSeries.isUnit_of_distinguished_mul_sub_mem_maximalIdeal_pow
    P₀ P₁ hP (isDistinguishedAt_map_coupledMonicDivisor d φ x₀ x₁ hP hx)
    hdegree u (q : PowerSeries B) hu c hprecision hproductclose

end MvPolynomial
