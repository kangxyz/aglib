/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.MvPolynomial.CoupledQuotientPrecision
public import Aglib.RingTheory.PowerSeries.PolynomialApproximation
public import Mathlib.Tactic.Ring

/-!
# Formal parameters for the coupled finite remainder system

Weierstrass division by the square of one distinguished polynomial produces
short remainder parameters. The formal quotients are approximated by genuine
source polynomials using finite coefficient quotients. These choices solve
the coupled remainder system and retain square-times-mixed-ideal precision.
The lower-dimensional Artin approximation step is not assumed or proved here.
-/

@[expose] public section

namespace PowerSeries

variable {A B σ ι : Type*} [CommRing A] [CommRing B] [IsLocalRing B]
  [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

/-- The formal solution supplies the coupled finite system's initial parameters,
with source-polynomial quotient approximations and mixed-adic precision. -/
theorem exists_coupled_parameters_of_formal_solution
    (P : Polynomial B) (hP : P.IsDistinguishedAt (IsLocalRing.maximalIdeal B))
    (φ : A →+* B) (c : ℕ)
    (hφ : Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal B ^ c)).comp φ))
    (g : MvPolynomial σ (Polynomial A)) (F : ι → MvPolynomial σ (Polynomial A))
    (y : σ → PowerSeries B)
    (hg : (P : PowerSeries B) ∣ MvPolynomial.eval₂Hom
      (Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom φ)) y g)
    (hF : ∀ i, MvPolynomial.eval₂Hom
      (Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom φ)) y (F i) = 0) :
    ∃ (z : σ → Polynomial A) (b : σ × Fin (2 * P.natDegree) → B),
      let x := Sum.elim (fun j : Fin P.natDegree ↦ P.coeff j) b
      (∀ k, MvPolynomial.eval₂Hom φ x
        (MvPolynomial.coupledDivisibilityEquation P.natDegree z g k) = 0) ∧
      (∀ q : ι × Fin (2 * P.natDegree), MvPolynomial.eval₂Hom φ x
        (MvPolynomial.coupledSquareDivisibilityEquation P.natDegree z (F q.1) q.2) = 0) ∧
      (∀ s, ((MvPolynomial.coupledPolynomialValue P.natDegree z s).map
          (MvPolynomial.eval₂Hom φ x) : PowerSeries B) - y s ∈
        Ideal.span {((P ^ 2 : Polynomial B) : PowerSeries B)} *
          IsLocalRing.maximalIdeal (PowerSeries B) ^ c) := by
  classical
  have hP2 : (P ^ 2).IsDistinguishedAt (IsLocalRing.maximalIdeal B) := by
    simpa only [pow_two] using hP.mul hP
  have hfac : ((P ^ 2 : Polynomial B) : PowerSeries B).IsWeierstrassFactorization
      (P ^ 2) 1 := ⟨hP2, isUnit_one, by simp⟩
  have hdivision (s : σ) : ∃ (w : PowerSeries B) (r : Polynomial B),
      r.degree < (2 * P.natDegree : ℕ) ∧
        y s = ((P ^ 2 : Polynomial B) : PowerSeries B) * w + r := by
    obtain ⟨w, r, hr⟩ := (y s).exists_isWeierstrassDivision hfac.map_ne_zero
    refine ⟨w, r, ?_, hr.eq_mul_add⟩
    have hdeg := hr.degree_lt
    change r.degree < (((P ^ 2 : Polynomial B) : PowerSeries B).map
      (IsLocalRing.residue B)).order.toNat at hdeg
    rw [← hfac.natDegree_eq_toNat_order_map, hP.monic.natDegree_pow] at hdeg
    exact hdeg
  choose w r hrdeg hyeq using hdivision
  have hz (s : σ) : ∃ z : Polynomial A,
      (z.map φ : PowerSeries B) - w s ∈ IsLocalRing.maximalIdeal (PowerSeries B) ^ c :=
    exists_polynomial_map_sub_mem_maximalIdeal_pow φ c hφ (w s)
  choose z hz using hz
  let b : σ × Fin (2 * P.natDegree) → B := fun q ↦ (r q.1).coeff q.2
  let x := Sum.elim (fun j : Fin P.natDegree ↦ P.coeff j) b
  let v (s : σ) : Polynomial B := P ^ 2 * (z s).map φ + r s
  have hPcoeff : Polynomial.X ^ P.natDegree +
      ∑ j : Fin P.natDegree, Polynomial.C (P.coeff j) * Polynomial.X ^ (j : ℕ) = P := by
    rw [Fin.sum_univ_eq_sum_range
      (fun j ↦ Polynomial.C (P.coeff j) * Polynomial.X ^ j)]
    exact hP.monic.as_sum.symm
  have hrcoeff (s : σ) : (∑ j : Fin (2 * P.natDegree),
      Polynomial.C ((r s).coeff j) * Polynomial.X ^ (j : ℕ)) = r s :=
    (Polynomial.sum_fin (fun i a ↦ Polynomial.C a * Polynomial.X ^ i)
      (by simp) (hrdeg s)).trans (Polynomial.sum_C_mul_X_pow_eq (r s))
  have hmapP : (MvPolynomial.coupledMonicDivisor σ A P.natDegree).map
      (MvPolynomial.eval₂Hom φ x) = P := by
    rw [MvPolynomial.map_coupledMonicDivisor]
    exact hPcoeff
  have hmapv (s : σ) : (MvPolynomial.coupledPolynomialValue P.natDegree z s).map
      (MvPolynomial.eval₂Hom φ x) = v s := by
    rw [MvPolynomial.map_coupledPolynomialValue]
    simp only [x, b, Sum.elim_inl, Sum.elim_inr, hPcoeff, hrcoeff, v]
  have hmapsub (G : MvPolynomial σ (Polynomial A)) :
      (MvPolynomial.coupledPolynomialSubstitution P.natDegree z G).map
        (MvPolynomial.eval₂Hom φ x) = MvPolynomial.eval₂Hom (Polynomial.mapRingHom φ) v G := by
    rw [MvPolynomial.map_coupledPolynomialSubstitution]
    simp only [x, b, Sum.elim_inl, Sum.elim_inr, hPcoeff, hrcoeff, v]
  have hv (s : σ) : (v s : PowerSeries B) - y s =
      ((P ^ 2 : Polynomial B) : PowerSeries B) * ((z s).map φ - w s) := by
    simp only [v, Polynomial.coe_add, Polynomial.coe_mul, hyeq]
    ring
  have hvmem (s : σ) : (v s : PowerSeries B) - y s ∈
      Ideal.span {((P ^ 2 : Polynomial B) : PowerSeries B)} *
        IsLocalRing.maximalIdeal (PowerSeries B) ^ c :=
    Ideal.mem_span_singleton_mul.mpr ⟨_, hz s, (hv s).symm⟩
  have hvdvd (s : σ) : ((P ^ 2 : Polynomial B) : PowerSeries B) ∣ y s - v s := by
    have h : ((P ^ 2 : Polynomial B) : PowerSeries B) ∣ (v s : PowerSeries B) - y s :=
      ⟨_, hv s⟩
    simpa only [neg_sub] using h.neg_right
  have hvdvdP (s : σ) : (P : PowerSeries B) ∣ y s - v s := by
    apply dvd_trans ?_ (hvdvd s)
    rw [Polynomial.coe_pow]
    exact dvd_pow_self (P : PowerSeries B) (by decide : 2 ≠ 0)
  have hgpoly : (MvPolynomial.coupledMonicDivisor σ A P.natDegree).map
      (MvPolynomial.eval₂Hom φ x) ∣
      (MvPolynomial.coupledPolynomialSubstitution P.natDegree z g).map
        (MvPolynomial.eval₂Hom φ x) := by
    rw [hmapP, hmapsub]
    exact (eval₂_dvd_iff_polynomial_of_sub_dvd P hP y v hvdvdP φ g).mp hg
  have hFpoly (i : ι) : (MvPolynomial.coupledMonicDivisor σ A P.natDegree).map
      (MvPolynomial.eval₂Hom φ x) ^ 2 ∣
      (MvPolynomial.coupledPolynomialSubstitution P.natDegree z (F i)).map
        (MvPolynomial.eval₂Hom φ x) := by
    rw [hmapP, hmapsub]
    apply (eval₂_dvd_iff_polynomial_of_sub_dvd (P ^ 2) hP2 y v hvdvd φ (F i)).mp
    rw [hF i]
    exact dvd_zero _
  have hsystem := (MvPolynomial.coupledDivisibilitySystem_iff P.natDegree z φ x g F).mpr
    ⟨hgpoly, hFpoly⟩
  exact ⟨z, b, hsystem.1, hsystem.2, fun s ↦ by rw [hmapv]; exact hvmem s⟩

end PowerSeries
