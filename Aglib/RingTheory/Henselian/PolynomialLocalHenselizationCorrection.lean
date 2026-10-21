/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationDivisibility
public import Aglib.RingTheory.Henselian.RectangularCorrection

/-!
# Correcting the actual higher-henselization polynomial point

Source polynomial factorizations of the equations and their literal Jacobian
determinant are combined with formal quotient estimates. The actual comparison
maps descend these estimates, after which determinant-squared correction is
applied in the higher henselization itself. This is the correction consumer,
not the lower-dimensional existence theorem for the parameter solution.
-/

@[expose] public section

namespace PolynomialLocalHenselization

open MvPolynomial

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Correct the source point in the actual higher henselization using the
quotients produced by the finite remainder system. -/
theorem exists_zero_of_selected_polynomial_quotient_estimates
    {ν : Type*} (e : σ ↪ ν) (n c : ℕ) (hc : 0 < c)
    (F : σ → MvPolynomial ν (Polynomial (PolynomialLocalHenselization R n)))
    (v : ν → Polynomial (PolynomialLocalHenselization R n))
    (P q : Polynomial (PolynomialLocalHenselization R n))
    (Q : σ → Polynomial (PolynomialLocalHenselization R n))
    (hg : eval v (Matrix.det (Matrix.of fun i j ↦ pderiv (e j) (F i))) = P * q)
    (hf : ∀ i, eval v (F i) = P ^ 2 * Q i)
    (hq : IsUnit (q.map (toFormalSeries R n).toRingHom :
      PowerSeries (PolynomialLocalRing.FormalSeries R n)))
    (hQ : ∀ i, ((Q i).map (toFormalSeries R n).toRingHom :
      PowerSeries (PolynomialLocalRing.FormalSeries R n)) ∈
        IsLocalRing.maximalIdeal (PowerSeries (PolynomialLocalRing.FormalSeries R n)) ^ c) :
    ∃ y : ν → PolynomialLocalHenselization R (n + 1),
      (∀ i, eval y (MvPolynomial.map (polynomialEvaluation R n).toRingHom (F i)) = 0) ∧
      ∀ i, y i - polynomialEvaluation R n (v i) ∈
        IsLocalRing.maximalIdeal (PolynomialLocalHenselization R (n + 1)) ^ c := by
  let ψ := (polynomialEvaluation R n).toRingHom
  let y₀ := fun i ↦ ψ (v i)
  let F₀ := fun i ↦ MvPolynomial.map ψ (F i)
  let a := IsLocalRing.maximalIdeal (PolynomialLocalHenselization R (n + 1)) ^ c
  have heval (p : MvPolynomial ν (Polynomial (PolynomialLocalHenselization R n))) :
      ψ (eval v p) = eval y₀ (MvPolynomial.map ψ p) := by
    rw [eval_map, eval₂_comp]
    rfl
  have hdet : ψ (eval v (Matrix.det (Matrix.of fun i j ↦ pderiv (e j) (F i)))) =
      Matrix.det (Matrix.of fun i j ↦ eval y₀ (pderiv (e j) (F₀ i))) := by
    rw [eval₂_comp]
    change (eval₂Hom ψ y₀) (Matrix.det (Matrix.of fun i j ↦ pderiv (e j) (F i))) = _
    rw [RingHom.map_det]
    congr 1
    apply Matrix.ext
    intro i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      F₀, pderiv_map, eval_map, coe_eval₂Hom]
  have ha : a ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal
      (PolynomialLocalHenselization R (n + 1))).ne_top (Ideal.pow_le_self hc.ne')
  have herror (i : σ) : eval y₀ (F₀ i) ∈
      Ideal.span {Matrix.det (Matrix.of fun i j ↦ eval y₀ (pderiv (e j) (F₀ i))) ^ 2} * a := by
    have h := polynomialEvaluation_mem_minor_sq_mul_of_formal_quotients R n c
      P q (Q i) (eval v (Matrix.det (Matrix.of fun i j ↦ pderiv (e j) (F i))))
      (eval v (F i)) hg (hf i) hq (hQ i)
    change ψ (eval v (F i)) ∈
      Ideal.span {ψ (eval v (Matrix.det (Matrix.of fun i j ↦ pderiv (e j) (F i)))) ^ 2} * a at h
    rw [hdet, heval] at h
    exact h
  obtain ⟨y, hy, _, _, hclose⟩ :=
    HenselianLocalRing.exists_eval_eq_zero_of_mem_embedding_det_sq_mul e F₀ y₀ a ha herror
  exact ⟨y, hy, hclose⟩


/-- Correct the source point in the actual higher henselization using the
quotients produced by the finite remainder system. -/
theorem exists_zero_of_polynomial_quotient_estimates
    (n c : ℕ) (hc : 0 < c)
    (F : σ → MvPolynomial σ (Polynomial (PolynomialLocalHenselization R n)))
    (v : σ → Polynomial (PolynomialLocalHenselization R n))
    (P q : Polynomial (PolynomialLocalHenselization R n))
    (Q : σ → Polynomial (PolynomialLocalHenselization R n))
    (hg : eval v (Matrix.det (Matrix.of fun i j ↦ pderiv j (F i))) = P * q)
    (hf : ∀ i, eval v (F i) = P ^ 2 * Q i)
    (hq : IsUnit (q.map (toFormalSeries R n).toRingHom :
      PowerSeries (PolynomialLocalRing.FormalSeries R n)))
    (hQ : ∀ i, ((Q i).map (toFormalSeries R n).toRingHom :
      PowerSeries (PolynomialLocalRing.FormalSeries R n)) ∈
        IsLocalRing.maximalIdeal (PowerSeries (PolynomialLocalRing.FormalSeries R n)) ^ c) :
    ∃ y : σ → PolynomialLocalHenselization R (n + 1),
      (∀ i, eval y (MvPolynomial.map (polynomialEvaluation R n).toRingHom (F i)) = 0) ∧
      ∀ i, y i - polynomialEvaluation R n (v i) ∈
        IsLocalRing.maximalIdeal (PolynomialLocalHenselization R (n + 1)) ^ c := by
  exact exists_zero_of_selected_polynomial_quotient_estimates R
    (Function.Embedding.refl σ) n c hc F v P q Q hg hf hq hQ

end PolynomialLocalHenselization
