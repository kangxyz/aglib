/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# A DVR as the closed unit ball of an actual norm

Source: `R5Lab.Aglib.Analysis.Normed.Field.DVR`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. The actual objects, maps, norm choices,
universes, and stated hypotheses are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace NormedField
universe u
/-- Compatibility of an actual DVR fraction-field inclusion with the given norm:
its image is exactly the norm's closed unit ball. No curve or discriminant is
mentioned, and no formula for valuations is assumed. -/
def NormCompatible (R F : Type u) [CommRing R] [NormedField F] [Algebra R F] : Prop :=
  ∀ x : F, ‖x‖ ≤ 1 ↔ ∃ r : R, algebraMap R F r = x

namespace NormCompatible
variable {R F : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [NormedField F] [Algebra R F] [IsFractionRing R F]
  (H : NormCompatible R F)

include H

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
@[nolint unusedArguments]
theorem norm_map_le_one [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] (r : R) :
  ‖algebraMap R F r‖ ≤ 1 :=
  (H _).2 ⟨r, rfl⟩

theorem norm_map_unit (u : Rˣ) : ‖algebraMap R F (u : R)‖ = 1 := by
  apply le_antisymm (H.norm_map_le_one _)
  have he : algebraMap R F (u : R) * algebraMap R F (↑u⁻¹ : R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hn := congrArg norm he
  rw [norm_mul, norm_one] at hn
  calc
    1 = ‖algebraMap R F (u : R)‖ * ‖algebraMap R F (↑u⁻¹ : R)‖ := hn.symm
    _ ≤ ‖algebraMap R F (u : R)‖ * 1 :=
      mul_le_mul_of_nonneg_left (H.norm_map_le_one _) (norm_nonneg _)
    _ = _ := mul_one _

omit [IsDomain R] [IsDiscreteValuationRing R] H in
@[nolint unusedArguments]
theorem norm_map_irreducible_pos [IsDomain R] [IsDiscreteValuationRing R] (_H : NormCompatible R
  F) {π : R} (hπ : Irreducible π) :
    0 < ‖algebraMap R F π‖ :=
  norm_pos_iff.mpr ((map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hπ.ne_zero)

theorem norm_map_irreducible_lt_one {π : R} (hπ : Irreducible π) :
    ‖algebraMap R F π‖ < 1 := by
  refine lt_of_le_of_ne (H.norm_map_le_one _) ?_
  intro he
  have hi : ‖(algebraMap R F π)⁻¹‖ ≤ 1 := by rw [norm_inv, he, inv_one]
  obtain ⟨r, hr⟩ := (H _).1 hi
  apply hπ.not_isUnit
  apply isUnit_iff_exists_inv.mpr
  refine ⟨r, (IsFractionRing.injective R F) ?_⟩
  rw [map_mul, map_one, hr, mul_inv_cancel₀]
  exact (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hπ.ne_zero

/-- The normalized valuation/norm relation is derived from the closed-unit-ball
compatibility and the DVR's unit-times-uniformizer factorization. -/
theorem norm_eq_pow_valuation {π r : R} (hπ : Irreducible π) (hr : r ≠ 0) :
    ‖algebraMap R F r‖ = ‖algebraMap R F π‖ ^ (IsDiscreteValuationRing.addVal R r).toNat := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hπ
  rw [IsDiscreteValuationRing.addVal_def' u hπ, ENat.toNat_natCast,
    map_mul, map_pow, norm_mul, norm_pow, H.norm_map_unit, one_mul]

theorem valuation_le_of_norm_ge {x y : R} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ‖algebraMap R F y‖ ≤ ‖algebraMap R F x‖) :
    (IsDiscreteValuationRing.addVal R x).toNat ≤
      (IsDiscreteValuationRing.addVal R y).toNat := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [H.norm_eq_pow_valuation hπ hx, H.norm_eq_pow_valuation hπ hy] at h
  exact (pow_le_pow_iff_right_of_lt_one₀
    (H.norm_map_irreducible_pos hπ) (H.norm_map_irreducible_lt_one hπ)).mp h

theorem valuation_eq_of_norm_eq {x y : R} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ‖algebraMap R F x‖ = ‖algebraMap R F y‖) :
    (IsDiscreteValuationRing.addVal R x).toNat =
      (IsDiscreteValuationRing.addVal R y).toNat :=
  Nat.le_antisymm (H.valuation_le_of_norm_ge hx hy h.symm.le)
    (H.valuation_le_of_norm_ge hy hx h.le)

end NormCompatible
end NormedField
