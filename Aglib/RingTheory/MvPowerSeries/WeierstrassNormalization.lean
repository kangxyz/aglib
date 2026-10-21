/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPowerSeries.FinLastEquiv
public import Aglib.RingTheory.MvPowerSeries.WeightedNormalization
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation

/-!
# Weierstrass normalization by triangular formal coordinates

A formal series nonzero over the residue field can be made a native
Weierstrass divisor by an explicit triangular change of coordinates and
isolation of the last variable. The residue field may be finite or imperfect.
No completeness is assumed here: completeness is needed for the subsequent
Weierstrass division and preparation, not for coordinate normalization.
-/

@[expose] public section

namespace PowerSeries

variable {R σ : Type*} [CommRing R] [IsLocalRing R]

/-- Nonzero residue specialization of the constant coefficients detects a
Weierstrass divisor over a local formal-series coefficient ring. -/
theorem map_residue_ne_zero_of_map_constantCoeff_residue_ne_zero
    (g : PowerSeries (MvPowerSeries σ R))
    (hg : g.map ((IsLocalRing.residue R).comp MvPowerSeries.constantCoeff) ≠ 0) :
    g.map (IsLocalRing.residue (MvPowerSeries σ R)) ≠ 0 := by
  intro hz
  apply hg
  apply PowerSeries.ext
  intro k
  rw [coeff_map, map_zero, RingHom.comp_apply]
  apply (IsLocalRing.residue_eq_zero_iff _).mpr
  by_contra hk
  have hu : IsUnit (MvPowerSeries.constantCoeff (coeff k g)) :=
    IsLocalRing.notMem_maximalIdeal.mp hk
  have hu' : IsUnit (coeff k g) := MvPowerSeries.isUnit_iff_constantCoeff.mpr hu
  have hh : IsLocalRing.residue (MvPowerSeries σ R) (coeff k g) = 0 := by
    simpa only [coeff_map, map_zero] using congrArg (coeff k) hz
  exact (hu'.map (IsLocalRing.residue (MvPowerSeries σ R))).ne_zero hh

end PowerSeries

namespace MvPowerSeries

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- A nonzero residue series becomes a Weierstrass divisor after an actual
triangular coordinate automorphism. -/
theorem exists_triangular_map_residue_ne_zero (n : ℕ)
    (f : MvPowerSeries (Fin (n + 1)) R)
    (hf : map (IsLocalRing.residue R) f ≠ 0) :
    ∃ (w : Fin (n + 1) → ℕ) (hw : ∀ i, 0 < w i),
      w (Fin.last n) = 1 ∧
      (finLastEquiv R n
        (triangularAlgEquiv (Fin.last n) w (fun i _ ↦ hw i) f)).map
          (IsLocalRing.residue (MvPowerSeries (Fin n) R)) ≠ 0 := by
  obtain ⟨w, hw, hp, hne⟩ := exists_pos_weight_subst_ne_zero n
    (map (IsLocalRing.residue R) f) hf
  refine ⟨w, hw, hp, ?_⟩
  apply PowerSeries.map_residue_ne_zero_of_map_constantCoeff_residue_ne_zero
  have haxis : PowerSeries.map (IsLocalRing.residue R)
      (killCompl (axisEmbedding (Fin.last n))
        (triangularAlgEquiv (Fin.last n) w (fun i _ ↦ hw i) f)) ≠ 0 := by
    rw [killCompl_axis_triangularAlgEquiv _ _ _ hp]
    change map (IsLocalRing.residue R)
      (subst (fun i ↦ (X () : MvPowerSeries Unit R) ^ w i) f) ≠ 0
    rw [map_subst (hasSubst_X_pow_weight () w hw)]
    simpa only [map_pow, map_X] using hne
  have hident :
      PowerSeries.map ((IsLocalRing.residue R).comp constantCoeff)
        (finLastEquiv R n (triangularAlgEquiv (Fin.last n) w (fun i _ ↦ hw i) f)) =
      PowerSeries.map (IsLocalRing.residue R)
        (killCompl (axisEmbedding (Fin.last n))
          (triangularAlgEquiv (Fin.last n) w (fun i _ ↦ hw i) f)) := by
    rw [← map_constantCoeff_finLastEquiv]
    apply PowerSeries.ext
    intro k
    simp only [PowerSeries.coeff_map, RingHom.comp_apply]
  rwa [hident]

/-- The normalized series satisfies the native Weierstrass-divisor predicate. -/
theorem exists_triangular_isWeierstrassDivisor (n : ℕ)
    (f : MvPowerSeries (Fin (n + 1)) R)
    (hf : map (IsLocalRing.residue R) f ≠ 0) :
    ∃ (w : Fin (n + 1) → ℕ) (hw : ∀ i, 0 < w i),
      w (Fin.last n) = 1 ∧
      (finLastEquiv R n
        (triangularAlgEquiv (Fin.last n) w (fun i _ ↦ hw i) f)).IsWeierstrassDivisor := by
  obtain ⟨w, hw, hp, hne⟩ := exists_triangular_map_residue_ne_zero n f hf
  exact ⟨w, hw, hp, PowerSeries.IsWeierstrassDivisor.of_map_ne_zero hne⟩

end MvPowerSeries
