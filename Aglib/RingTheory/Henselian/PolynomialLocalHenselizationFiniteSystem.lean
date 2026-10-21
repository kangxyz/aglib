/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PowerSeries.FiniteDivisibilityReduction
public import Aglib.Algebra.MvPolynomial.CoupledUnitQuotient
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationCorrection

/-!
# Finite equations whose source solutions give actual henselized solutions

The coefficient ring and formal target are the actual lower-dimensional
henselization and its formal-series target. Their proved quotient comparison
supplies coefficient density. A nearby source solution of the finite remainder
equations gives an exact solution in the actual higher henselization, retaining
formal mixed-adic precision. Existence of that source parameter solution is
left to induction; coefficient reduction and a nonzero Jacobian minor are also
not asserted by this theorem.
-/

@[expose] public section

namespace PolynomialLocalHenselization

open MvPolynomial

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ)
  {σ : Type*} [Fintype σ] [DecidableEq σ]

local notation "Aₙ" => PolynomialLocalHenselization R n
local notation "Bₙ" => PolynomialLocalRing.FormalSeries R n

/-- Actual lower-dimensional remainder equations suffice for an exact solution
in the higher henselization, conditional on a nearby source parameter solution.
The equations are finitely indexed; their parameter index is finite whenever `ν` is finite. -/
theorem exists_finite_system_for_selected_correction
    {ν : Type*} (selected : σ ↪ ν)
    (F : σ → MvPolynomial ν (Polynomial Aₙ)) (y : ν → PowerSeries Bₙ)
    (P : Polynomial Bₙ) (hP : P.IsDistinguishedAt (IsLocalRing.maximalIdeal Bₙ))
    (u : PowerSeries Bₙ) (hu : IsUnit u) (c : ℕ) (hc : P.natDegree < c)
    (hF : ∀ i, eval₂Hom
      (Polynomial.coeToPowerSeries.ringHom.comp
        (Polynomial.mapRingHom (toFormalSeries R n).toRingHom))
      y (F i) = 0)
    (hg : eval₂Hom
      (Polynomial.coeToPowerSeries.ringHom.comp
        (Polynomial.mapRingHom (toFormalSeries R n).toRingHom))
      y (Matrix.det (Matrix.of fun i j ↦ pderiv (selected j) (F i))) = (P : PowerSeries Bₙ) * u) :
    ∃ (z : ν → Polynomial Aₙ) (b : ν × Fin (2 * P.natDegree) → Bₙ),
      let x₀ := Sum.elim (fun j : Fin P.natDegree ↦ P.coeff j) b
      let g := Matrix.det (Matrix.of fun i j ↦ pderiv (selected j) (F i))
      (∀ k, eval₂Hom (toFormalSeries R n).toRingHom x₀
        (coupledDivisibilityEquation P.natDegree z g k) = 0) ∧
      (∀ q : σ × Fin (2 * P.natDegree), eval₂Hom (toFormalSeries R n).toRingHom x₀
        (coupledSquareDivisibilityEquation P.natDegree z (F q.1) q.2) = 0) ∧
      ∀ t : Fin P.natDegree ⊕ (ν × Fin (2 * P.natDegree)) → Aₙ,
        (∀ k, toFormalSeries R n (t k) - x₀ k ∈ IsLocalRing.maximalIdeal Bₙ ^ c) →
        ((∀ k, eval₂Hom (RingHom.id Aₙ) t
          (coupledDivisibilityEquation P.natDegree z g k) = 0) ∧
        ∀ q : σ × Fin (2 * P.natDegree), eval₂Hom (RingHom.id Aₙ) t
          (coupledSquareDivisibilityEquation P.natDegree z (F q.1) q.2) = 0) →
        ∃ y' : ν → PolynomialLocalHenselization R (n + 1),
          (∀ i, eval y' (MvPolynomial.map (polynomialEvaluation R n).toRingHom (F i)) = 0) ∧
          ∀ i, iteratedFormalMap R n (y' i) - y i ∈
            IsLocalRing.maximalIdeal (PowerSeries Bₙ) ^ c := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal Bₙ) Bₙ :=
    PolynomialLocalRing.formalSeries_isAdicComplete R n
  let φ := (toFormalSeries R n).toRingHom
  let g := Matrix.det (Matrix.of fun i j ↦ pderiv (selected j) (F i))
  obtain ⟨z, b, hg₀, hF₀, hreduce⟩ := PowerSeries.exists_finite_divisibility_reduction
    P hP φ c (quotient_mk_comp_toFormalSeries_surjective R n c) g F y ⟨u, hg⟩ hF
  let x₀ := Sum.elim (fun j : Fin P.natDegree ↦ P.coeff j) b
  have hmapP : (coupledMonicDivisor ν Aₙ P.natDegree).map (eval₂Hom φ x₀) = P := by
    rw [map_coupledMonicDivisor]
    change Polynomial.X ^ P.natDegree +
      ∑ j : Fin P.natDegree, Polynomial.C (P.coeff j) * Polynomial.X ^ (j : ℕ) = P
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ Polynomial.C (P.coeff j) * Polynomial.X ^ j)]
    exact hP.monic.as_sum.symm
  refine ⟨z, b, hg₀, hF₀, ?_⟩
  intro t ht hs
  obtain ⟨hgdiv, _, hvclose, _, hQsmall⟩ := hreduce t ht hs
  let e := eval₂Hom (RingHom.id Aₙ) t
  let x₁ := fun k ↦ φ (t k)
  let p := (coupledMonicDivisor ν Aₙ P.natDegree).map e
  let v := fun i ↦ (coupledPolynomialValue P.natDegree z i).map e
  let q := (coupledPolynomialSubstitution P.natDegree z g /ₘ
    coupledMonicDivisor ν Aₙ P.natDegree).map e
  let Q := fun i ↦ (coupledSquareQuotient P.natDegree z (F i)).map e
  have hev (H : MvPolynomial (Fin P.natDegree ⊕ (ν × Fin (2 * P.natDegree))) Aₙ) :
      eval₂Hom φ x₁ H = φ (e H) := by
    simp only [e, map_eval₂Hom, RingHom.comp_id, x₁]
  have hmap (H : Polynomial (MvPolynomial
      (Fin P.natDegree ⊕ (ν × Fin (2 * P.natDegree))) Aₙ)) :
      (H.map e).map φ = H.map (eval₂Hom φ x₁) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext fun H ↦ (hev H).symm
  have hsub (H : MvPolynomial ν (Polynomial Aₙ)) :
      (coupledPolynomialSubstitution P.natDegree z H).map e = eval v H := by
    change Polynomial.mapRingHom e
      (eval₂Hom (Polynomial.mapRingHom C) (coupledPolynomialValue P.natDegree z) H) = _
    rw [map_eval₂Hom, Polynomial.mapRingHom_comp]
    have hC : e.comp C = RingHom.id Aₙ := by ext a; simp [e]
    rw [hC]
    simp only [Polynomial.mapRingHom_id, Polynomial.coe_mapRingHom, coe_eval₂Hom, eval₂_id, v]
  have hgsource : eval v g = p * q := by
    have hrem : (coupledPolynomialSubstitution P.natDegree z g).map e %ₘ p = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd
        ((coupledMonicDivisor_monic P.natDegree).map e)).mpr hgdiv
    have h := Polynomial.modByMonic_add_div
      ((coupledPolynomialSubstitution P.natDegree z g).map e) p
    rw [hrem, zero_add] at h
    rw [hsub] at h
    have hq : q = eval v g /ₘ p := by
      dsimp only [q]
      rw [Polynomial.map_divByMonic _ (coupledMonicDivisor_monic P.natDegree), hsub]
    rw [hq]
    exact h.symm
  have hfsource (i : σ) : eval v (F i) = p ^ 2 * Q i := by
    have h := eq_sq_mul_map_coupledSquareQuotient P.natDegree z (RingHom.id Aₙ) t
      (F i) (fun k ↦ hs.2 (i, k))
    rw [hsub] at h
    exact h
  have hx (k) : x₁ k - x₀ k ∈ IsLocalRing.maximalIdeal Bₙ :=
    Ideal.pow_le_self (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hc)) (ht k)
  have hqformal : IsUnit (q.map φ : PowerSeries Bₙ) := by
    rw [hmap]
    refine isUnit_map_coupled_divByMonic_of_formal_factorization
      P.natDegree z φ x₀ x₁ g y u hu ?_ ?_ c hc hx ?_ ?_
    · simpa only [hmapP] using hP
    · simpa only [hmapP] using hg
    · intro i
      rw [← hmap]
      exact hvclose i
    · intro k
      rw [hev, hs.1 k, map_zero]
  obtain ⟨y', hy', hyclose⟩ := exists_zero_of_selected_polynomial_quotient_estimates R selected n c
    (lt_of_le_of_lt (Nat.zero_le _) hc) F v p q Q hgsource hfsource hqformal hQsmall
  refine ⟨y', hy', ?_⟩
  intro i
  have hclose := (iteratedFormalMap_mem_maximalIdeal_pow_iff R n c _).mpr (hyclose i)
  rw [map_sub] at hclose
  have hsquare := RingHom.congr_fun (iteratedFormalMap_comp_polynomialEvaluation R n) (v i)
  change iteratedFormalMap R n (polynomialEvaluation R n (v i)) =
    ((v i).map φ : PowerSeries Bₙ) at hsquare
  rw [hsquare] at hclose
  have hv : ((v i).map φ : PowerSeries Bₙ) - y i ∈
      IsLocalRing.maximalIdeal (PowerSeries Bₙ) ^ c := hvclose i
  simpa only [sub_add_sub_cancel] using
    (IsLocalRing.maximalIdeal (PowerSeries Bₙ) ^ c).add_mem hclose hv


/-- The actual lower-dimensional finite system suffices for an exact solution
in the higher henselization. This does not assert existence of its source solution. -/
theorem exists_finite_system_for_correction
    (F : σ → MvPolynomial σ (Polynomial Aₙ)) (y : σ → PowerSeries Bₙ)
    (P : Polynomial Bₙ) (hP : P.IsDistinguishedAt (IsLocalRing.maximalIdeal Bₙ))
    (u : PowerSeries Bₙ) (hu : IsUnit u) (c : ℕ) (hc : P.natDegree < c)
    (hF : ∀ i, eval₂Hom
      (Polynomial.coeToPowerSeries.ringHom.comp
        (Polynomial.mapRingHom (toFormalSeries R n).toRingHom))
      y (F i) = 0)
    (hg : eval₂Hom
      (Polynomial.coeToPowerSeries.ringHom.comp
        (Polynomial.mapRingHom (toFormalSeries R n).toRingHom))
      y (Matrix.det (Matrix.of fun i j ↦ pderiv j (F i))) = (P : PowerSeries Bₙ) * u) :
    ∃ (z : σ → Polynomial Aₙ) (b : σ × Fin (2 * P.natDegree) → Bₙ),
      let x₀ := Sum.elim (fun j : Fin P.natDegree ↦ P.coeff j) b
      let g := Matrix.det (Matrix.of fun i j ↦ pderiv j (F i))
      (∀ k, eval₂Hom (toFormalSeries R n).toRingHom x₀
        (coupledDivisibilityEquation P.natDegree z g k) = 0) ∧
      (∀ q : σ × Fin (2 * P.natDegree), eval₂Hom (toFormalSeries R n).toRingHom x₀
        (coupledSquareDivisibilityEquation P.natDegree z (F q.1) q.2) = 0) ∧
      ∀ t : Fin P.natDegree ⊕ (σ × Fin (2 * P.natDegree)) → Aₙ,
        (∀ k, toFormalSeries R n (t k) - x₀ k ∈ IsLocalRing.maximalIdeal Bₙ ^ c) →
        ((∀ k, eval₂Hom (RingHom.id Aₙ) t
          (coupledDivisibilityEquation P.natDegree z g k) = 0) ∧
        ∀ q : σ × Fin (2 * P.natDegree), eval₂Hom (RingHom.id Aₙ) t
          (coupledSquareDivisibilityEquation P.natDegree z (F q.1) q.2) = 0) →
        ∃ y' : σ → PolynomialLocalHenselization R (n + 1),
          (∀ i, eval y' (MvPolynomial.map (polynomialEvaluation R n).toRingHom (F i)) = 0) ∧
          ∀ i, iteratedFormalMap R n (y' i) - y i ∈
            IsLocalRing.maximalIdeal (PowerSeries Bₙ) ^ c := by
  exact exists_finite_system_for_selected_correction R n
    (Function.Embedding.refl σ) F y P hP u hu c hc hF hg

end PolynomialLocalHenselization
