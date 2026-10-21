/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.MvPolynomial.UniversalDivisibilityEquations
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

/-!
# From formal divisibility to finite polynomial equations

Weierstrass division gives polynomial representatives of a formal point modulo
a distinguished polynomial. The native quotient algebra equivalence reflects
polynomial divisibility. Consequently the representatives' coefficients solve
the universal finite divisibility equations, while their congruence to the
original formal point is retained. This is a formal reduction, not descent of
these coefficients to an algebraic power-series or henselized subring.
-/

@[expose] public section

namespace Polynomial

variable {B : Type*} [CommRing B] {I : Ideal B} [IsAdicComplete I B]

/-- The native distinguished-polynomial quotient equivalence reflects divisibility. -/
theorem IsDistinguishedAt.coe_dvd_coe_iff {P : Polynomial B}
    (hP : P.IsDistinguishedAt I) (q : Polynomial B) :
    (P : PowerSeries B) ∣ (q : PowerSeries B) ↔ P ∣ q := by
  constructor
  · intro h
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hP.algEquivQuotient.injective
    rw [map_zero]
    have hzero : Ideal.Quotient.mk (Ideal.span {(P : PowerSeries B)})
        (q : PowerSeries B) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h)
    simpa [IsDistinguishedAt.algEquivQuotient_apply] using hzero
  · exact fun h ↦ _root_.map_dvd coeToPowerSeries.ringHom h

end Polynomial

namespace PowerSeries

variable {A B σ : Type*} [CommRing A] [CommRing B] [IsLocalRing B]
  [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

/-- Replacing a formal point by polynomial representatives modulo a distinguished
polynomial preserves and reflects the equation's divisibility. -/
theorem eval₂_dvd_iff_polynomial_of_sub_dvd (P : Polynomial B)
    (hP : P.IsDistinguishedAt (IsLocalRing.maximalIdeal B))
    (y : σ → PowerSeries B) (r : σ → Polynomial B)
    (hr : ∀ i, (P : PowerSeries B) ∣ y i - r i)
    (φ : A →+* B) (F : MvPolynomial σ (Polynomial A)) :
    (P : PowerSeries B) ∣ MvPolynomial.eval₂Hom
      (Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom φ)) y F ↔
      P ∣ MvPolynomial.eval₂Hom (Polynomial.mapRingHom φ) r F := by
  let J : Ideal (PowerSeries B) := Ideal.span {(P : PowerSeries B)}
  let π := Ideal.Quotient.mk J
  have hpoint : (fun i ↦ π (y i)) = (fun i ↦ π (r i : PowerSeries B)) := by
    funext i
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    exact Ideal.mem_span_singleton.mpr (hr i)
  have hcoe :
      (MvPolynomial.eval₂Hom (Polynomial.mapRingHom φ) r F : PowerSeries B) =
      MvPolynomial.eval₂Hom
        (Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom φ))
        (fun i ↦ (r i : PowerSeries B)) F := by
    simpa only [Polynomial.coeToPowerSeries.ringHom_apply] using
      MvPolynomial.map_eval₂Hom (Polynomial.mapRingHom φ) r
        Polynomial.coeToPowerSeries.ringHom F
  have heval : π (MvPolynomial.eval₂Hom
      (Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom φ)) y F) =
      π (MvPolynomial.eval₂Hom (Polynomial.mapRingHom φ) r F : PowerSeries B) := by
    rw [hcoe, MvPolynomial.map_eval₂Hom, MvPolynomial.map_eval₂Hom, hpoint]
  rw [← hP.coe_dvd_coe_iff]
  simpa only [π, J, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using
    (show π (MvPolynomial.eval₂Hom
      (Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom φ)) y F) = 0 ↔
        π (MvPolynomial.eval₂Hom (Polynomial.mapRingHom φ) r F : PowerSeries B) = 0
      from by rw [heval])

/-- Formal divisibility supplies an actual solution of the finite universal
coefficient equations and preserves the original formal point modulo `P`. -/
theorem exists_remainder_coefficients_solving_divisibility {ι : Type*}
    (P : Polynomial B) (hP : P.IsDistinguishedAt (IsLocalRing.maximalIdeal B))
    (φ : A →+* B) (F : ι → MvPolynomial σ (Polynomial A)) (y : σ → PowerSeries B)
    (hF : ∀ i, (P : PowerSeries B) ∣
      MvPolynomial.eval₂Hom
        (Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom φ)) y (F i)) :
    ∃ b : σ × Fin P.natDegree → B,
      (∀ s, (P : PowerSeries B) ∣ y s -
        ((∑ j : Fin P.natDegree, Polynomial.C (b (s, j)) * Polynomial.X ^ (j : ℕ)) :
          Polynomial B)) ∧
      ∀ z : ι × Fin P.natDegree,
        MvPolynomial.eval₂Hom φ
          (Sum.elim (fun j : Fin P.natDegree ↦ P.coeff j) b)
          (MvPolynomial.universalDivisibilityEquation P.natDegree (F z.1) z.2) = 0 := by
  classical
  have hfac : (P : PowerSeries B).IsWeierstrassFactorization P 1 :=
    ⟨hP, isUnit_one, by simp⟩
  have hrem (s : σ) : ∃ r : Polynomial B,
      r.degree < P.natDegree ∧ (P : PowerSeries B) ∣ y s - r := by
    obtain ⟨q, r, hr⟩ := (y s).exists_isWeierstrassDivision hfac.map_ne_zero
    refine ⟨r, ?_, q, ?_⟩
    · have hdeg := hr.degree_lt
      change r.degree < ((P : PowerSeries B).map (IsLocalRing.residue B)).order.toNat at hdeg
      rw [← hfac.natDegree_eq_toNat_order_map] at hdeg
      exact hdeg
    · rw [hr.eq_mul_add, add_sub_cancel_right]
  choose r hrdeg hr using hrem
  have hrcoeff (s : σ) :
      (∑ j : Fin P.natDegree, Polynomial.C ((r s).coeff j) * Polynomial.X ^ (j : ℕ)) = r s :=
    (Polynomial.sum_fin (fun i c ↦ Polynomial.C c * Polynomial.X ^ i)
      (by simp) (hrdeg s)).trans (Polynomial.sum_C_mul_X_pow_eq (r s))
  refine ⟨fun z ↦ (r z.1).coeff z.2, ?_, ?_⟩
  · intro s
    simpa only [hrcoeff] using hr s
  · rw [MvPolynomial.universalDivisibilitySystem_iff]
    intro i
    have hPcoeff :
        Polynomial.X ^ P.natDegree +
          ∑ j : Fin P.natDegree, Polynomial.C (P.coeff j) * Polynomial.X ^ (j : ℕ) = P := by
      rw [Fin.sum_univ_eq_sum_range
        (fun j ↦ Polynomial.C (P.coeff j) * Polynomial.X ^ j)]
      exact hP.monic.as_sum.symm
    simp only [Sum.elim_inl, Sum.elim_inr, hPcoeff, hrcoeff]
    exact (eval₂_dvd_iff_polynomial_of_sub_dvd P hP y r hr φ (F i)).mp (hF i)

end PowerSeries
