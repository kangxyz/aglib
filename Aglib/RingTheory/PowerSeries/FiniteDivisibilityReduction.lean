/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PowerSeries.CoupledFormalParameters

/-!
# Finite divisibility reduction with source solutions and formal precision

The formal solution supplies a coefficient system with bounded coefficient
indices. It is finite when the unknown and equation families are finite. Any
nearby solution in the original coefficient ring yields genuine source-ring
divisibility and square-times-ideal formal error. The existence of a nearby
source solution is the remaining lower-dimensional approximation step; this
result does not assume that step as a global ring property or assert Artin
approximation. The divisor must still be compared with the Jacobian minor by
a unit before determinant correction can be applied.
-/

@[expose] public section

namespace PowerSeries

variable {A B σ ι : Type*} [CommRing A] [CommRing B] [IsLocalRing B]
  [IsAdicComplete (IsLocalRing.maximalIdeal B) B]

/-- A formal solution reduces to a coefficient system over the original ring,
and every nearby source solution has the required square-ideal precision.
Finite unknown and equation families give a finite coefficient system. -/
theorem exists_finite_divisibility_reduction
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
      let x₀ := Sum.elim (fun j : Fin P.natDegree ↦ P.coeff j) b
      (∀ k, MvPolynomial.eval₂Hom φ x₀
        (MvPolynomial.coupledDivisibilityEquation P.natDegree z g k) = 0) ∧
      (∀ q : ι × Fin (2 * P.natDegree), MvPolynomial.eval₂Hom φ x₀
        (MvPolynomial.coupledSquareDivisibilityEquation P.natDegree z (F q.1) q.2) = 0) ∧
      ∀ t : Fin P.natDegree ⊕ (σ × Fin (2 * P.natDegree)) → A,
        (∀ k, φ (t k) - x₀ k ∈ IsLocalRing.maximalIdeal B ^ c) →
        ((∀ k, MvPolynomial.eval₂Hom (RingHom.id A) t
          (MvPolynomial.coupledDivisibilityEquation P.natDegree z g k) = 0) ∧
        ∀ q : ι × Fin (2 * P.natDegree), MvPolynomial.eval₂Hom (RingHom.id A) t
          (MvPolynomial.coupledSquareDivisibilityEquation P.natDegree z (F q.1) q.2) = 0) →
        let e := MvPolynomial.eval₂Hom (RingHom.id A) t
        let p := (MvPolynomial.coupledMonicDivisor σ A P.natDegree).map e
        (p ∣ (MvPolynomial.coupledPolynomialSubstitution P.natDegree z g).map e) ∧
        (∀ i, p ^ 2 ∣ (MvPolynomial.coupledPolynomialSubstitution P.natDegree z (F i)).map e) ∧
        (∀ s, (((MvPolynomial.coupledPolynomialValue P.natDegree z s).map e).map φ :
          PowerSeries B) - y s ∈ IsLocalRing.maximalIdeal (PowerSeries B) ^ c) ∧
        (∀ i, (((MvPolynomial.coupledPolynomialSubstitution P.natDegree z (F i)).map e).map φ :
          PowerSeries B) ∈ Ideal.span {((p.map φ ^ 2 : Polynomial B) : PowerSeries B)} *
            IsLocalRing.maximalIdeal (PowerSeries B) ^ c) ∧
        ∀ i, (((MvPolynomial.coupledSquareQuotient P.natDegree z (F i)).map e).map φ :
          PowerSeries B) ∈ IsLocalRing.maximalIdeal (PowerSeries B) ^ c := by
  classical
  obtain ⟨z, b, hg₀, hF₀, hr⟩ :=
    exists_coupled_parameters_of_formal_solution P hP φ c hφ g F y hg hF
  let x₀ := Sum.elim (fun j : Fin P.natDegree ↦ P.coeff j) b
  have hmapP : (MvPolynomial.coupledMonicDivisor σ A P.natDegree).map
      (MvPolynomial.eval₂Hom φ x₀) = P := by
    rw [MvPolynomial.map_coupledMonicDivisor]
    change Polynomial.X ^ P.natDegree +
      ∑ j : Fin P.natDegree, Polynomial.C (P.coeff j) * Polynomial.X ^ (j : ℕ) = P
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ Polynomial.C (P.coeff j) * Polynomial.X ^ j)]
    exact hP.monic.as_sum.symm
  refine ⟨z, b, hg₀, hF₀, ?_⟩
  intro t ht hs
  let x₁ := fun k ↦ φ (t k)
  let e := MvPolynomial.eval₂Hom (RingHom.id A) t
  have hev (Q : MvPolynomial (Fin P.natDegree ⊕ (σ × Fin (2 * P.natDegree))) A) :
      MvPolynomial.eval₂Hom φ x₁ Q = φ (e Q) := by
    symm
    simp only [e, MvPolynomial.map_eval₂Hom, RingHom.comp_id, x₁]
  have hmap (Q : Polynomial (MvPolynomial
      (Fin P.natDegree ⊕ (σ × Fin (2 * P.natDegree))) A)) :
      (Q.map e).map φ = Q.map (MvPolynomial.eval₂Hom φ x₁) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext fun Q ↦ (hev Q).symm
  have hC : (IsLocalRing.maximalIdeal B).map (C : B →+* PowerSeries B) ≤
      IsLocalRing.maximalIdeal (PowerSeries B) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    simpa only [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      isUnit_iff_constantCoeff, constantCoeff_C] using ha
  have hCpow : (IsLocalRing.maximalIdeal B ^ c).map (C : B →+* PowerSeries B) ≤
      IsLocalRing.maximalIdeal (PowerSeries B) ^ c := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hC c
  have htC (k) : C (x₁ k - x₀ k) ∈ IsLocalRing.maximalIdeal (PowerSeries B) ^ c :=
    hCpow (Ideal.mem_map_of_mem C (ht k))
  have hnew (i : ι) (k : Fin (2 * P.natDegree)) : MvPolynomial.eval₂Hom φ x₁
      (MvPolynomial.coupledSquareDivisibilityEquation P.natDegree z (F i) k) = 0 := by
    rw [hev, hs.2 (i, k), map_zero]
  have hsource := (MvPolynomial.coupledDivisibilitySystem_iff P.natDegree z
    (RingHom.id A) t g F).mp hs
  refine ⟨hsource.1, hsource.2, ?_, ?_, ?_⟩
  · intro s
    rw [hmap]
    have hd := MvPolynomial.coe_map_eval₂_sub_mem φ x₁ x₀
      (IsLocalRing.maximalIdeal (PowerSeries B) ^ c) htC
      (MvPolynomial.coupledPolynomialValue P.natDegree z s)
    have ho : ((MvPolynomial.coupledPolynomialValue P.natDegree z s).map
        (MvPolynomial.eval₂Hom φ x₀) : PowerSeries B) - y s ∈
        IsLocalRing.maximalIdeal (PowerSeries B) ^ c := Ideal.mul_le_right (hr s)
    simpa only [sub_add_sub_cancel] using
      (IsLocalRing.maximalIdeal (PowerSeries B) ^ c).add_mem hd ho
  · intro i
    rw [hmap, hmap]
    apply MvPolynomial.coupled_eval_mem_sq_mul_of_formal_solution
      P.natDegree z φ x₀ x₁ (F i) y _
    · simpa only [hmapP] using hP
    · exact hF i
    · simpa only [hmapP] using hr
    · exact htC
    · exact hnew i
  · intro i
    rw [hmap]
    apply MvPolynomial.coe_map_coupledSquareQuotient_mem_of_formal_solution
      P.natDegree z φ x₀ x₁ (F i) y _
    · simpa only [hmapP] using hP
    · exact hF i
    · simpa only [hmapP] using hr
    · exact htC

end PowerSeries
