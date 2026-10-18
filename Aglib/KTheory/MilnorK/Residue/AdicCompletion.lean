/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.DiscreteValuationRing
public import Aglib.KTheory.MilnorK.Residue.Restriction

/-!
# Actual DVR residue under completion

The completion fraction-field map preserves the original uniformizer. Its
residue map is the literal map inverted by the canonical completion residue
equivalence. No norm or completion tensor decomposition is assumed.
-/

@[expose] public noncomputable section

namespace MilnorK.DVR

open IsLocalRing

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- Completion commutes with the canonical tame residue on every Milnor class. -/
theorem residue_completion_restrict (n : ℕ) :
    (map n (ResidueField.map
      (algebraMap R (AdicCompletion (maximalIdeal R) R)))).comp (residue R F n) =
      (residue (AdicCompletion (maximalIdeal R) R)
        (FractionRing (AdicCompletion (maximalIdeal R) R)) n).comp
          (map (n + 1) (AdicCompletion.fractionRingMap R F)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  exact residue_restrict (algebraMap R (AdicCompletion (maximalIdeal R) R))
    (AdicCompletion.fractionRingMap R F)
    (AdicCompletion.fractionRingMap_algebraMap R F) hπ
    (AdicCompletion.irreducible_algebraMap R π hπ) n

/-- Identifying the completed residue field by its actual inverse map recovers
exactly the original residue, not a degree multiple of it. -/
theorem residue_completion_identification (n : ℕ) (x : K F (n + 1)) :
    map n (AdicCompletion.residueFieldEquiv R).toRingHom
      (residue (AdicCompletion (maximalIdeal R) R)
        (FractionRing (AdicCompletion (maximalIdeal R) R)) n
          (map (n + 1) (AdicCompletion.fractionRingMap R F) x)) =
      residue R F n x := by
  have hc := LinearMap.congr_fun (residue_completion_restrict R F n) x
  simp only [LinearMap.comp_apply] at hc
  rw [← hc]
  rw [← LinearMap.comp_apply, ← map_comp]
  have h : (AdicCompletion.residueFieldEquiv R).toRingHom.comp
      (ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) =
        RingHom.id (ResidueField R) := by
    ext z
    exact AdicCompletion.residueFieldEquiv_map R z
  rw [h, map_id, LinearMap.id_apply]

end MilnorK.DVR
