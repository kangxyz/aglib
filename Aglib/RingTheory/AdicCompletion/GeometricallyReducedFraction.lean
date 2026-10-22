/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.DiscreteValuationRing
public import Aglib.RingTheory.Nilpotent.GeometricallyReduced

/-!
# Geometric reducedness of the actual completed fraction field

The coefficient condition uses the maximal-ideal completion itself and the
canonical `FractionRing.liftAlgebra` action. It is an independent geometric
property, not a desingularization or approximation hypothesis. Characteristic
zero supplies the condition by perfectness of the original fraction field.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace AdicCompletion

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The actual maximal-ideal completion of a domain DVR is a faithful algebra. -/
theorem faithfulSMul_maximalIdeal :
    FaithfulSMul R (AdicCompletion (maximalIdeal R) R) := by
  apply (faithfulSMul_iff_algebraMap_injective _ _).mpr
  intro x y h
  apply AdicCompletion.of_injective (maximalIdeal R) R
  simpa only [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply] using h

/-- The actual completed fraction field is geometrically reduced over the
original fraction field, with its canonical lifted coefficient action. -/
def HasGeometricallyReducedFractionCompletion : Prop :=
  letI := faithfulSMul_maximalIdeal R
  letI := FractionRing.liftAlgebra R
    (FractionRing (AdicCompletion (maximalIdeal R) R))
  Algebra.IsGeometricallyReduced (FractionRing R)
    (FractionRing (AdicCompletion (maximalIdeal R) R))

/-- Unfold the coefficient condition using any witness of faithfulness for the
same completion algebra. The induced fraction action is still the canonical one. -/
theorem hasGeometricallyReducedFractionCompletion_iff
    [FaithfulSMul R (AdicCompletion (maximalIdeal R) R)] :
    HasGeometricallyReducedFractionCompletion R ↔
      letI := FractionRing.liftAlgebra R
        (FractionRing (AdicCompletion (maximalIdeal R) R))
      Algebra.IsGeometricallyReduced (FractionRing R)
        (FractionRing (AdicCompletion (maximalIdeal R) R)) :=
  Iff.rfl

/-- Perfectness of the actual original fraction field supplies the intrinsic
completion condition. No perfection of the residue field is required. -/
theorem hasGeometricallyReducedFractionCompletion_of_perfectField
    [PerfectField (FractionRing R)] : HasGeometricallyReducedFractionCompletion R := by
  let := faithfulSMul_maximalIdeal R
  let := FractionRing.liftAlgebra R
    (FractionRing (AdicCompletion (maximalIdeal R) R))
  exact Algebra.isGeometricallyReduced_field_of_perfectField (FractionRing R)
    (FractionRing (AdicCompletion (maximalIdeal R) R))

/-- Every characteristic-zero domain DVR satisfies the intrinsic coefficient
condition, including mixed-characteristic DVRs with imperfect residue field. -/
theorem hasGeometricallyReducedFractionCompletion_of_charZero
    [CharZero R] : HasGeometricallyReducedFractionCompletion R := by
  let : CharZero (FractionRing R) := charZero_of_injective_ringHom
    (f := algebraMap R (FractionRing R)) (IsFractionRing.injective R (FractionRing R))
  exact hasGeometricallyReducedFractionCompletion_of_perfectField R

end AdicCompletion
