/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationInductionStep
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationNormalization
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationCoefficientSplit
public import Aglib.RingTheory.MvPowerSeries.TriangularPreparation

/-!
# Solving selected polynomial systems by lower-dimensional approximation

The determinant is normalized by an actual triangular change of geometric
coordinates. Splitting off the last variable gives the prepared system consumed
by the full lower-dimensional induction hypothesis. Source coordinates are
then transported back using the actual henselization automorphism.

The residue-nonvanishing hypothesis is retained here: over an excellent DVR,
nonzero in the formal fraction field alone does not imply it.
-/

@[expose] public section

noncomputable section

namespace PolynomialLocalHenselization

open MvPolynomial IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The polynomial coefficient embedding has its original formal restriction. -/
theorem toFormalSeries_polynomialToHenselization (n : ℕ)
    (p : MvPolynomial (Fin n) R) :
    toFormalSeries R n (polynomialToHenselization R n p) =
      PolynomialLocalRing.polynomialToFormalSeries R n p := by
  have h := AlgHom.congr_fun (toFormalSeries_comp_of R n)
    (algebraMap (MvPolynomial (Fin n) R) (PolynomialLocalRing R n) p)
  change toFormalSeries R n (polynomialToHenselization R n p) =
    PolynomialLocalRing.toFormalSeries R n
      (algebraMap (MvPolynomial (Fin n) R) (PolynomialLocalRing R n) p) at h
  exact h.trans (PolynomialLocalRing.toFormalSeries_algebraMap R n p)

omit [IsNoetherianRing R] in
/-- The source triangular change preserves the literal polynomial coefficient embedding. -/
theorem triangularAlgEquiv_polynomialToHenselization (n : ℕ) (p : Fin n)
    (e : Fin n → ℕ) (he : ∀ i, i ≠ p → 0 < e i) (f : MvPolynomial (Fin n) R) :
    triangularAlgEquiv R n p e he (polynomialToHenselization R n f) =
      polynomialToHenselization R n (MvPolynomial.triangularAlgEquiv R p e f) := by
  change triangularAlgEquiv R n p e he
    (algebraMap (PolynomialLocalRing R n) (PolynomialLocalHenselization R n)
      (algebraMap (MvPolynomial (Fin n) R) (PolynomialLocalRing R n) f)) = _
  rw [triangularAlgEquiv_algebraMap, PolynomialLocalRing.triangularAlgEquiv_algebraMap]
  rfl

/-- The lower full approximation hypothesis solves a selected system whenever
its selected determinant is nonzero modulo the completed coefficient maximal ideal. -/
theorem exists_zero_of_selected_polynomial_system_of_residue_ne_zero (n : ℕ)
    (ih : ∀ (s t : ℕ)
      (E : Fin t → MvPolynomial (Fin s) (PolynomialLocalHenselization R n))
      (b : Fin s → PolynomialLocalRing.FormalSeries R n),
      (∀ i, eval₂ (toFormalSeries R n).toRingHom b (E i) = 0) →
      ∀ c : ℕ, ∃ a : Fin s → PolynomialLocalHenselization R n,
        (∀ i, eval a (E i) = 0) ∧
        ∀ j, toFormalSeries R n (a j) - b j ∈
          maximalIdeal (PolynomialLocalRing.FormalSeries R n) ^ c)
    {σ ν : Type*} [Fintype σ] [DecidableEq σ] [Finite ν] (selected : σ ↪ ν)
    (F : σ → MvPolynomial ν (MvPolynomial (Fin (n + 1)) R))
    (y : ν → PolynomialLocalRing.FormalSeries R (n + 1))
    (hF : ∀ i, eval₂ (PolynomialLocalRing.polynomialToFormalSeries R (n + 1)).toRingHom
      y (F i) = 0)
    (hg : MvPowerSeries.map (residue (AdicCompletion (maximalIdeal R) R))
      (eval₂ (PolynomialLocalRing.polynomialToFormalSeries R (n + 1)).toRingHom y
        (Matrix.det (Matrix.of fun i j => pderiv (selected j) (F i)))) ≠ 0) (c : ℕ) :
    ∃ x : ν → PolynomialLocalHenselization R (n + 1),
      (∀ i, eval₂ (polynomialToHenselization R (n + 1)).toRingHom x (F i) = 0) ∧
      ∀ j, toFormalSeries R (n + 1) (x j) - y j ∈
        maximalIdeal (PolynomialLocalRing.FormalSeries R (n + 1)) ^ c := by
  let Rhat := AdicCompletion (maximalIdeal R) R
  let : IsNoetherianRing Rhat := AdicCompletion.isNoetherianRing R (maximalIdeal R)
  let g := Matrix.det (Matrix.of fun i j => pderiv (selected j) (F i))
  let φ := (PolynomialLocalRing.polynomialToFormalSeries R (n + 1)).toRingHom
  let ψ := (polynomialToHenselization R (n + 1)).toRingHom
  obtain ⟨w, hw, _, P, u, hprep⟩ :=
    MvPowerSeries.exists_triangular_isWeierstrassFactorization n (eval₂ φ y g) hg
  let he := fun i (_ : i ≠ Fin.last n) => hw i
  let α := triangularAlgEquiv R (n + 1) (Fin.last n) w he
  let β := MvPowerSeries.triangularAlgEquiv (R := Rhat) (Fin.last n) w he
  let a := MvPolynomial.triangularAlgEquiv R (Fin.last n) w
  let θ := MvPowerSeries.finLastEquiv Rhat n
  let κ := (coefficientSplit R n).toRingHom.comp a.toRingHom
  let ρ := Polynomial.coeToPowerSeries.ringHom.comp
    (Polynomial.mapRingHom (toFormalSeries R n).toRingHom)
  let F' := fun i => MvPolynomial.map κ (F i)
  let y' := fun j => θ (β (y j))
  have hsource (p : MvPolynomial (Fin (n + 1)) R) :
      polynomialEvaluation R n (κ p) = α (ψ p) := by
    have h := AlgHom.congr_fun (polynomialEvaluation_comp_coefficientSplit R n) (a p)
    change polynomialEvaluation R n (κ p) = polynomialToHenselization R (n + 1) (a p) at h
    rw [h]
    exact (triangularAlgEquiv_polynomialToHenselization R (n + 1) (Fin.last n) w he p).symm
  have hcoeff (p : MvPolynomial (Fin (n + 1)) R) : ρ (κ p) = θ (β (φ p)) := by
    have h := RingHom.congr_fun (iteratedFormalMap_comp_polynomialEvaluation R n) (κ p)
    change iteratedFormalMap R n (polynomialEvaluation R n (κ p)) = ρ (κ p) at h
    rw [← h, hsource]
    change θ (toFormalSeries R (n + 1) (α (ψ p))) = _
    have ha := AlgHom.congr_fun
      (toFormalSeries_comp_triangularAlgEquiv R (n + 1) (Fin.last n) w he) (ψ p)
    change toFormalSeries R (n + 1) (α (ψ p)) = β (toFormalSeries R (n + 1) (ψ p)) at ha
    rw [ha]
    exact congrArg (fun z => θ (β z))
      (toFormalSeries_polynomialToHenselization R (n + 1) p)
  have heval (f : MvPolynomial ν (MvPolynomial (Fin (n + 1)) R)) :
      eval₂ ρ y' (MvPolynomial.map κ f) = θ (β (eval₂ φ y f)) := by
    rw [eval₂_map]
    have hc : ρ.comp κ = θ.toRingHom.comp (β.toRingHom.comp φ) := RingHom.ext hcoeff
    rw [hc]
    exact (hom_eval₂ f φ (θ.toRingHom.comp β.toRingHom) y).symm
  have hF' : ∀ i, eval₂Hom ρ y' (F' i) = 0 := by
    intro i
    change eval₂ ρ y' (MvPolynomial.map κ (F i)) = 0
    rw [heval, hF i, map_zero, map_zero]
  have hdet : Matrix.det (Matrix.of fun i j => pderiv (selected j) (F' i)) =
      MvPolynomial.map κ g := by
    rw [RingHom.map_det]
    congr 1
    apply Matrix.ext
    intro i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, F', pderiv_map]
  have hg' : eval₂Hom ρ y'
      (Matrix.det (Matrix.of fun i j => pderiv (selected j) (F' i))) =
        (P : PowerSeries (PolynomialLocalRing.FormalSeries R n)) * u := by
    rw [hdet]
    change eval₂ ρ y' (MvPolynomial.map κ g) = _
    rw [heval]
    exact hprep.eq_mul
  obtain ⟨x', hx', hclose⟩ := exists_zero_of_prepared_selected_system R n ih selected
    F' y' P hprep.isDistinguishedAt u hprep.isUnit hF' hg' c
  have hx : ∀ i, eval x'
      (MvPolynomial.map α.toRingHom (MvPolynomial.map ψ (F i))) = 0 := by
    intro i
    have hmap : (polynomialEvaluation R n).toRingHom.comp κ = α.toRingHom.comp ψ :=
      RingHom.ext hsource
    simpa only [F', MvPolynomial.map_map, hmap] using hx' i
  have hprecision : ∀ j, toFormalSeries R (n + 1) (x' j) - β (y j) ∈
      maximalIdeal (PolynomialLocalRing.FormalSeries R (n + 1)) ^ c := by
    intro j
    have hm : (maximalIdeal (PowerSeries (PolynomialLocalRing.FormalSeries R n)) ^ c).map
        θ.symm.toRingHom = maximalIdeal (PolynomialLocalRing.FormalSeries R (n + 1)) ^ c := by
      change (maximalIdeal (PowerSeries (PolynomialLocalRing.FormalSeries R n)) ^ c).map
        θ.symm.toRingEquiv = maximalIdeal (PolynomialLocalRing.FormalSeries R (n + 1)) ^ c
      rw [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal]
    have h := Ideal.mem_map_of_mem θ.symm.toRingHom (hclose j)
    rw [hm] at h
    change θ.symm (θ (toFormalSeries R (n + 1) (x' j)) - θ (β (y j))) ∈ _ at h
    simpa only [map_sub, AlgEquiv.symm_apply_apply] using h
  obtain ⟨x, hx, hclose⟩ := exists_solution_of_triangular_normalization R (n + 1)
    (Fin.last n) w he (fun i => MvPolynomial.map ψ (F i)) y c x' hx hprecision
  refine ⟨x, ?_, hclose⟩
  intro i
  simpa only [eval_map] using hx i

end PolynomialLocalHenselization
