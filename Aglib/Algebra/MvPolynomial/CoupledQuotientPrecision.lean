/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.MvPolynomial.CoupledDivisibilityEquations
public import Aglib.RingTheory.PowerSeries.DistinguishedQuotientPrecision

/-!
# Mixed-ideal precision after solving the coupled remainder equations

The old parameter values come from a point close to an exact formal solution.
The actual polynomial quotient is small by distinguished division. Parameter
congruence preserves its image in the full power-series quotient ring. Thus a
new solution of the square-remainder equations has error in its own divisor
squared times the prescribed ideal, not merely divisible by that square.
-/

@[expose] public section

namespace MvPolynomial

variable {A B κ σ : Type*} [CommRing A] [CommRing B]

/-- Parameter congruence controls the full series image of a polynomial in the parameters. -/
theorem coe_map_eval₂_sub_mem (φ : A →+* B) (x₁ x₀ : κ → B)
    (a : Ideal (PowerSeries B))
    (hx : ∀ k, PowerSeries.C (x₁ k - x₀ k) ∈ a)
    (Q : Polynomial (MvPolynomial κ A)) :
    (Q.map (eval₂Hom φ x₁) : PowerSeries B) -
      (Q.map (eval₂Hom φ x₀) : PowerSeries B) ∈ a := by
  let π := Ideal.Quotient.mk a
  have hcoeff : (π.comp PowerSeries.C).comp (eval₂Hom φ x₁) =
      (π.comp PowerSeries.C).comp (eval₂Hom φ x₀) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro k
      simp only [RingHom.comp_apply, eval₂Hom_X']
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      simpa only [map_sub] using hx k
  have hmaps : π.comp (Polynomial.coeToPowerSeries.ringHom.comp
        (Polynomial.mapRingHom (eval₂Hom φ x₁))) =
      π.comp (Polynomial.coeToPowerSeries.ringHom.comp
        (Polynomial.mapRingHom (eval₂Hom φ x₀))) := by
    apply Polynomial.ringHom_ext
    · intro c
      simpa only [RingHom.comp_apply, Polynomial.coe_mapRingHom,
        Polynomial.map_C, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_C] using RingHom.congr_fun hcoeff c
    · simp
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (RingHom.congr_fun hmaps Q)

variable [IsLocalRing B] [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

/-- The actual quotient at the new parameter point belongs to the prescribed
full-series ideal; no cancellation of an arbitrary divisor is used. -/
theorem coe_map_coupledSquareQuotient_mem_of_formal_solution
    (d : ℕ) (z : σ → Polynomial A) (φ : A →+* B)
    (x₀ x₁ : Fin d ⊕ (σ × Fin (2 * d)) → B)
    (F : MvPolynomial σ (Polynomial A)) (y : σ → PowerSeries B)
    (a : Ideal (PowerSeries B))
    (hP : ((coupledMonicDivisor σ A d).map (eval₂Hom φ x₀)).IsDistinguishedAt
      (IsLocalRing.maximalIdeal B))
    (hy : eval₂Hom
      (Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom φ)) y F = 0)
    (hr : ∀ i, ((coupledPolynomialValue d z i).map (eval₂Hom φ x₀) : PowerSeries B) -
      y i ∈ Ideal.span
        {((((coupledMonicDivisor σ A d).map (eval₂Hom φ x₀)) ^ 2 : Polynomial B) :
          PowerSeries B)} * a)
    (hx : ∀ k, PowerSeries.C (x₁ k - x₀ k) ∈ a) :
    ((coupledSquareQuotient d z F).map (eval₂Hom φ x₁) : PowerSeries B) ∈ a := by
  have hsub : (coupledPolynomialSubstitution d z F).map (eval₂Hom φ x₀) =
      eval₂Hom (Polynomial.mapRingHom φ)
        (fun i ↦ (coupledPolynomialValue d z i).map (eval₂Hom φ x₀)) F := by
    change Polynomial.mapRingHom (eval₂Hom φ x₀)
      (eval₂Hom (Polynomial.mapRingHom C) (coupledPolynomialValue d z) F) = _
    rw [map_eval₂Hom, Polynomial.mapRingHom_comp]
    have hC : (eval₂Hom φ x₀).comp C = φ := by ext c; simp
    rw [hC]
    simp only [Polynomial.coe_mapRingHom]
  have hsmall₀ : ((coupledSquareQuotient d z F).map (eval₂Hom φ x₀) :
      PowerSeries B) ∈ a := by
    unfold coupledSquareQuotient
    rw [Polynomial.map_divByMonic _ ((coupledMonicDivisor_monic d).pow 2),
      Polynomial.map_pow, hsub]
    exact PowerSeries.divByMonic_sq_mem_of_eval_eq_zero _ hP φ F y _ a hy hr
  have hsmall₁ : ((coupledSquareQuotient d z F).map (eval₂Hom φ x₁) :
      PowerSeries B) ∈ a := by
    have hdiff := coe_map_eval₂_sub_mem φ x₁ x₀ a hx (coupledSquareQuotient d z F)
    simpa only [sub_add_cancel] using a.add_mem hdiff hsmall₀
  exact hsmall₁

/-- Solving the coupled equations near the formal parameter point gives the
square-times-ideal error required by determinant correction. -/
theorem coupled_eval_mem_sq_mul_of_formal_solution
    (d : ℕ) (z : σ → Polynomial A) (φ : A →+* B)
    (x₀ x₁ : Fin d ⊕ (σ × Fin (2 * d)) → B)
    (F : MvPolynomial σ (Polynomial A)) (y : σ → PowerSeries B)
    (a : Ideal (PowerSeries B))
    (hP : ((coupledMonicDivisor σ A d).map (eval₂Hom φ x₀)).IsDistinguishedAt
      (IsLocalRing.maximalIdeal B))
    (hy : eval₂Hom
      (Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.mapRingHom φ)) y F = 0)
    (hr : ∀ i, ((coupledPolynomialValue d z i).map (eval₂Hom φ x₀) : PowerSeries B) -
      y i ∈ Ideal.span
        {((((coupledMonicDivisor σ A d).map (eval₂Hom φ x₀)) ^ 2 : Polynomial B) :
          PowerSeries B)} * a)
    (hx : ∀ k, PowerSeries.C (x₁ k - x₀ k) ∈ a)
    (hF : ∀ k, eval₂Hom φ x₁ (coupledSquareDivisibilityEquation d z F k) = 0) :
    ((coupledPolynomialSubstitution d z F).map (eval₂Hom φ x₁) : PowerSeries B) ∈
      Ideal.span
        {((((coupledMonicDivisor σ A d).map (eval₂Hom φ x₁)) ^ 2 : Polynomial B) :
          PowerSeries B)} * a := by
  have hsmall := coe_map_coupledSquareQuotient_mem_of_formal_solution
    d z φ x₀ x₁ F y a hP hy hr hx
  apply Ideal.mem_span_singleton_mul.mpr
  refine ⟨_, hsmall, ?_⟩
  rw [← Polynomial.coe_mul, ← eq_sq_mul_map_coupledSquareQuotient d z φ x₁ F hF]

end MvPolynomial
