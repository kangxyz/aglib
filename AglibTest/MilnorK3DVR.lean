/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.DVR
public import Lean.Util.CollectAxioms

/-! # Actual DVR consumers of the degree-three Milnor residue -/

@[expose] public noncomputable section

namespace AglibTest.MilnorK3DVR

open MilnorK.K2 MilnorK.K3

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The target is the Milnor K₂ of the actual residue field, not supplied residue data. -/
def actualResidue : MilnorK.K3.Group K →ₗ[ℤ] MilnorK.K2.Group (IsLocalRing.ResidueField R) :=
  MilnorK.K3.DVR.residue R K

/-- Every actual irreducible computes the same full homomorphism. -/
theorem every_uniformizer {π : R} (hπ : Irreducible π) :
    actualResidue (R := R) (K := K) =
      MilnorK.K3.DVR.residueWithUniformizer (K := K) hπ :=
  MilnorK.K3.DVR.residue_eq hπ

/-- The literal ring residue map determines the normalized symbol. -/
theorem original_residue_normalization {π : R} (hπ : Irreducible π) (u v : Rˣ) :
    actualResidue (R := R) (K := K)
      (symbol3 (MilnorK.K2.DVR.uniformizer (K := K) hπ)
        (MilnorK.K2.DVR.fieldUnits R K u)
        (MilnorK.K2.DVR.fieldUnits R K v)) =
      symbol (Units.map (IsLocalRing.residue R).toMonoidHom u)
        (Units.map (IsLocalRing.residue R).toMonoidHom v) :=
  MilnorK.K3.DVR.residue_uniformizer_ring_units hπ u v

open Lean in
run_cmd do
  for name in #[``MilnorK.K3.DVR.residueWithUniformizer,
      ``MilnorK.K3.DVR.residueWithUniformizer_independent,
      ``MilnorK.K3.DVR.residue,
      ``MilnorK.K3.DVR.residue_eq,
      ``MilnorK.K3.DVR.residue_ring_units,
      ``MilnorK.K3.DVR.residue_uniformizer_ring_units,
      ``actualResidue, ``every_uniformizer, ``original_residue_normalization] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual DVR Milnor K3 residue uses only standard Lean logical foundations."

end AglibTest.MilnorK3DVR
