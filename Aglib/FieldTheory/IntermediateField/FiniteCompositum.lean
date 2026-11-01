/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Dimension.Free

/-! # The native finite compositum inside a specified common field

A finite intermediate field over the original base generates a finite extension
of any larger coefficient field inside the same ambient field. The construction
uses the actual intermediate-field adjoin and inclusion, without generators or
an algebraicity assumption on the ambient extension.
-/

@[expose] public noncomputable section

namespace IntermediateField

universe u v w

variable {k : Type u} (K : Type v) {Ω : Type w}
  [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω] [Algebra K Ω]
  [IsScalarTower k K Ω] (F : IntermediateField k Ω)

/-- The native compositum is finite over the larger coefficient field. -/
theorem finite_adjoin_intermediateField [Module.Finite k F] :
    Module.Finite K (adjoin K (F : Set Ω)) := by
  exact Module.rank_lt_aleph0_iff.mp
    ((adjoin_rank_le_of_isAlgebraic_right K F).trans_lt (Module.rank_lt_aleph0 k F))

/-- The original intermediate field lies in the same native compositum. -/
theorem le_restrictScalars_adjoin : F ≤ (adjoin K (F : Set Ω)).restrictScalars k :=
  subset_adjoin K (F : Set Ω)

/-- The inclusion retains the original base-field algebra action. -/
def finiteCompositumInclusion : F →ₐ[k] adjoin K (F : Set Ω) :=
  inclusion (le_restrictScalars_adjoin K F)

/-- The whole ambient-field triangle of the actual compositum inclusion. -/
@[simp] theorem val_comp_finiteCompositumInclusion :
    ((adjoin K (F : Set Ω)).val.restrictScalars k).comp (finiteCompositumInclusion K F) =
      F.val := by
  ext x
  rfl

/-- The whole scalar triangle retains the original map from the base field. -/
@[simp] theorem finiteCompositumInclusion_comp_algebraMap :
    (finiteCompositumInclusion K F).toRingHom.comp (algebraMap k F) =
      algebraMap k (adjoin K (F : Set Ω)) := by
  exact RingHom.ext fun x => (finiteCompositumInclusion K F).commutes x

end IntermediateField
