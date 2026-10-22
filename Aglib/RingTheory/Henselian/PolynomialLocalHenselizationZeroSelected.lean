/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationSelectedApproximation
public import Aglib.RingTheory.Henselian.PolynomialLocalHenselizationPrecision
public import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# The zero-variable selected-system consumer

The actual local-ring correction theorem is transported through the original
completion comparison. With zero geometric variables, a determinant nonzero
modulo the completed coefficient maximal ideal is a unit. This is not a field
base case: the coefficient ring may be any local Noetherian ring, including a
mixed-characteristic DVR. Singular systems still require the geometric
selected-system reduction before this theorem applies.
-/

@[expose] public noncomputable section

namespace PolynomialLocalHenselization

open MvPolynomial IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The zero-variable case of residue-nonzero selected-system approximation,
with coefficients in the actual polynomial-origin henselization. -/
theorem exists_zero_of_selected_system_zero_of_residue_ne_zero
    {σ ν : Type*} [Fintype σ] [DecidableEq σ] (selected : σ ↪ ν)
    (F : σ → MvPolynomial ν (PolynomialLocalHenselization R 0))
    (y : ν → PolynomialLocalRing.FormalSeries R 0)
    (hF : ∀ i, eval₂ (toFormalSeries R 0).toRingHom y (F i) = 0)
    (hg : MvPowerSeries.map (residue (AdicCompletion (maximalIdeal R) R))
      (eval₂ (toFormalSeries R 0).toRingHom y
        (Matrix.det (Matrix.of fun i j => pderiv (selected j) (F i)))) ≠ 0)
    (c : ℕ) :
    ∃ x : ν → PolynomialLocalHenselization R 0,
      (∀ i, eval x (F i) = 0) ∧
      ∀ j, toFormalSeries R 0 (x j) - y j ∈
        maximalIdeal (PolynomialLocalRing.FormalSeries R 0) ^ c := by
  let L := PolynomialLocalRing R 0
  let C := AdicCompletion (maximalIdeal L) L
  let e := PolynomialLocalRing.completionEquiv R 0
  let φ := (Henselization.toAdicCompletion L).toRingHom
  let z := fun j => e.symm (y j)
  let g := Matrix.det (Matrix.of fun i j => pderiv (selected j) (F i))
  have hmap : e.toRingHom.comp φ = (toFormalSeries R 0).toRingHom := by
    exact congrArg AlgHom.toRingHom (completionFormalMap_eq_toFormalSeries R 0)
  have heval (p : MvPolynomial ν (PolynomialLocalHenselization R 0)) :
      e (eval₂ φ z p) = eval₂ (toFormalSeries R 0).toRingHom y p := by
    change e.toRingHom (eval₂ φ z p) = _
    rw [hom_eval₂, hmap]
    congr 1
    funext j
    exact e.apply_symm_apply (y j)
  have hF' (i : σ) : eval₂ φ z (F i) = 0 := by
    apply e.injective
    rw [map_zero, heval, hF]
  have hu : IsUnit (eval₂ (toFormalSeries R 0).toRingHom y g) := by
    apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
    apply (residue_ne_zero_iff_isUnit _).mp
    intro hzero
    apply hg
    apply (MvPowerSeries.isEmptyEquiv (Fin 0)
      (ResidueField (AdicCompletion (maximalIdeal R) R))).injective
    change MvPowerSeries.constantCoeff
      (MvPowerSeries.map (residue (AdicCompletion (maximalIdeal R) R))
        (eval₂ (toFormalSeries R 0).toRingHom y g)) =
      MvPowerSeries.constantCoeff 0
    rw [MvPowerSeries.constantCoeff_map, map_zero]
    exact hzero
  have hu' : IsUnit (eval₂ φ z g) := by
    have h := hu.map e.symm.toRingHom
    change IsUnit (e.symm (eval₂ (toFormalSeries R 0).toRingHom y g)) at h
    rw [← heval g, AlgEquiv.symm_apply_apply] at h
    exact h
  obtain ⟨x, hx, hclose⟩ := Henselization.exists_zero_of_selected_system_of_residue_ne_zero L
    selected F z hF' ((residue_ne_zero_iff_isUnit _).mpr hu') c
  refine ⟨x, hx, ?_⟩
  intro j
  have hm : (maximalIdeal C ^ c).map e.toRingHom =
      maximalIdeal (PolynomialLocalRing.FormalSeries R 0) ^ c := by
    change (maximalIdeal C ^ c).map e.toRingEquiv = _
    rw [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal]
  have h := Ideal.mem_map_of_mem e.toRingHom (hclose j)
  rw [hm] at h
  have hs (a : PolynomialLocalHenselization R 0) :
      e (Henselization.toAdicCompletion L a) = toFormalSeries R 0 a :=
    RingHom.congr_fun hmap a
  change e (Henselization.toAdicCompletion L (x j) - e.symm (y j)) ∈
    maximalIdeal (PolynomialLocalRing.FormalSeries R 0) ^ c at h
  simpa only [map_sub, hs, AlgEquiv.apply_symm_apply] using h

end PolynomialLocalHenselization
