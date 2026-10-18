/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.DiscreteValuationRing
public import Aglib.RingTheory.DiscreteValuationRing.FractionBaseChange

/-! # Actual fraction-field scalar extension to the completed base DVR -/

@[expose] public noncomputable section

namespace AdicCompletion

open IsLocalRing
open scoped TensorProduct

variable (R F : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- The original fraction field acts through the actual completion fraction map. -/
@[instance_reducible] def fractionCompletionAlgebra :
    Algebra F (FractionRing (AdicCompletion (maximalIdeal R) R)) :=
  (fractionRingMap R F).toAlgebra

/-- The actual fraction-completion map respects the original base ring. -/
theorem fractionCompletionIsScalarTower :
    letI := fractionCompletionAlgebra R F
    IsScalarTower R F (FractionRing (AdicCompletion (maximalIdeal R) R)) := by
  let := fractionCompletionAlgebra R F
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (fractionRingMap_algebraMap R F r).symm

/-- Generic base change to the completed fraction field is obtained by inverting
an actual original uniformizer, with no tensor-isomorphism hypothesis. -/
def fractionCompletionBaseChangeAlgEquiv
    (E : Type*) [CommRing E] [Algebra R E] [Algebra F E] [IsScalarTower R F E] :
    letI := fractionCompletionAlgebra R F
    FractionRing (AdicCompletion (maximalIdeal R) R) ⊗[F] E ≃ₐ[AdicCompletion (maximalIdeal R) R]
      AdicCompletion (maximalIdeal R) R ⊗[R] E := by
  letI := fractionCompletionAlgebra R F
  letI := fractionCompletionIsScalarTower R F
  exact IsDiscreteValuationRing.fractionBaseChangeAlgEquiv R
    (AdicCompletion (maximalIdeal R) R) F (FractionRing (AdicCompletion (maximalIdeal R) R))
    (AdicCompletion.of_injective (maximalIdeal R) R) E

@[simp] theorem fractionCompletionBaseChangeAlgEquiv_one_tmul
    (E : Type*) [CommRing E] [Algebra R E] [Algebra F E] [IsScalarTower R F E] (x : E) :
    letI := fractionCompletionAlgebra R F
    fractionCompletionBaseChangeAlgEquiv R F E (1 ⊗ₜ[F] x) = 1 ⊗ₜ[R] x := by
  simp [fractionCompletionBaseChangeAlgEquiv,
    IsDiscreteValuationRing.fractionBaseChangeAlgEquiv]

end AdicCompletion
