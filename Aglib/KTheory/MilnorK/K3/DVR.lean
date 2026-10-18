/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.ResidueChange
public import Aglib.KTheory.MilnorK.K2.DVR.Uniformizer

/-!
# The actual Milnor K₃ residue of a discrete valuation ring

The elementary residue data are constructed from the DVR, its actual fraction
field, and the actual residue ring homomorphism. The degree-three residue is
independent of the irreducible uniformizer chosen for that construction. Its
normalization uses embedded ring units and their literal residue-field units.
No finite norm or rational-function reciprocity is assumed here.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.DVR

open MilnorK.K2

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The actual degree-three residue constructed using a specified DVR uniformizer. -/
def residueWithUniformizer {π : R} (hπ : Irreducible π) :
    Group K →ₗ[ℤ] MilnorK.K2.Group (IsLocalRing.ResidueField R) :=
  residue3 (MilnorK.K2.DVR.data (K := K) hπ) (MilnorK.K2.DVR.unitReductionCompatible hπ)

/-- Changing the actual irreducible uniformizer leaves the complete residue map unchanged. -/
theorem residueWithUniformizer_independent {π π' : R}
    (hπ : Irreducible π) (hπ' : Irreducible π') :
    residueWithUniformizer (K := K) hπ' = residueWithUniformizer (K := K) hπ :=
  residue3_eq_of_unitPart_change (MilnorK.K2.DVR.data hπ) (MilnorK.K2.DVR.data hπ')
    (MilnorK.K2.DVR.unitReductionCompatible hπ) (MilnorK.K2.DVR.unitReductionCompatible hπ')
    (MilnorK.K2.DVR.uniformizerChange hπ hπ') (fun _ => rfl)
    (MilnorK.K2.DVR.unitPart_change hπ hπ')

variable (R K) in
/-- The degree-three residue of a DVR, using the proved existence of a uniformizer. -/
def residue : Group K →ₗ[ℤ] MilnorK.K2.Group (IsLocalRing.ResidueField R) :=
  residueWithUniformizer (K := K) (IsDiscreteValuationRing.exists_irreducible R).choose_spec

/-- The chosen construction agrees with the construction using every actual uniformizer. -/
theorem residue_eq {π : R} (hπ : Irreducible π) :
    residue R K = residueWithUniformizer (K := K) hπ :=
  residueWithUniformizer_independent hπ
    (IsDiscreteValuationRing.exists_irreducible R).choose_spec

/-- A symbol of three embedded ring units has zero actual residue. -/
theorem residue_ring_units (a b c : Rˣ) :
    residue R K (symbol3 (MilnorK.K2.DVR.fieldUnits R K a)
      (MilnorK.K2.DVR.fieldUnits R K b) (MilnorK.K2.DVR.fieldUnits R K c)) = 0 := by
  let hπ := (IsDiscreteValuationRing.exists_irreducible R).choose_spec
  exact residue3_units (MilnorK.K2.DVR.data (K := K) hπ)
    (MilnorK.K2.DVR.unitReductionCompatible hπ) _ _ _
    (MilnorK.K2.DVR.value_fieldUnits R K a) (MilnorK.K2.DVR.value_fieldUnits R K b)
    (MilnorK.K2.DVR.value_fieldUnits R K c)

/-- The actual first-slot normalization uses the original ring residue map on units. -/
theorem residue_uniformizer_ring_units {π : R} (hπ : Irreducible π) (u v : Rˣ) :
    residue R K (symbol3 (MilnorK.K2.DVR.uniformizer (K := K) hπ)
      (MilnorK.K2.DVR.fieldUnits R K u) (MilnorK.K2.DVR.fieldUnits R K v)) =
      symbol (Units.map (IsLocalRing.residue R).toMonoidHom u)
        (Units.map (IsLocalRing.residue R).toMonoidHom v) := by
  rw [residue_eq hπ]
  have h := residue3_uniformizer_units (MilnorK.K2.DVR.data (K := K) hπ)
    (MilnorK.K2.DVR.unitReductionCompatible hπ)
    (MilnorK.K2.DVR.fieldUnits R K u) (MilnorK.K2.DVR.fieldUnits R K v)
    (MilnorK.K2.DVR.value_fieldUnits R K u) (MilnorK.K2.DVR.value_fieldUnits R K v)
  change residueWithUniformizer (K := K) hπ _ =
    symbol (MilnorK.K2.DVR.unitResidue hπ (MilnorK.K2.DVR.fieldUnits R K u))
      (MilnorK.K2.DVR.unitResidue hπ (MilnorK.K2.DVR.fieldUnits R K v)) at h
  simpa only [MilnorK.K2.DVR.data, MilnorK.K2.DVR.unitResidue_fieldUnits] using h

end MilnorK.K3.DVR
