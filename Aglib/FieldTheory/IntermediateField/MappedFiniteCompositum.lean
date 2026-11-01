/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.IntermediateField.FiniteCompositum

/-! # The original finite source field embedded in a common-field compositum

The existing intermediate-field image equivalence and original inclusion give
one map from the unchanged source field into the native compositum. All ambient
and scalar maps remain the original maps; no new field realization is selected.
-/

@[expose] public noncomputable section

namespace IntermediateField

universe u

variable {k L Ω : Type u} (K : Type u)
  [Field k] [Field L] [Field K] [Field Ω]
  [Algebra k L] [Algebra k K] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]
  (F : IntermediateField k L) (e : L →ₐ[k] Ω)

/-- The existing image equivalence retains finiteness of the actual source field. -/
theorem finite_mapped_adjoin [Module.Finite k F] :
    Module.Finite K (adjoin K ((F.map e : IntermediateField k Ω) : Set Ω)) := by
  let : Module.Finite k (F.map e) := LinearEquiv.finiteDimensional (F.equivMap e).toLinearEquiv
  exact finite_adjoin_intermediateField K (F.map e)

/-- The actual source-field map into the same native compositum. -/
def mappedFiniteCompositumInclusion :
    F →ₐ[k] adjoin K ((F.map e : IntermediateField k Ω) : Set Ω) :=
  (finiteCompositumInclusion K (F.map e)).comp (F.equivMap e).toAlgHom

/-- The full ambient equation uses the specified embedding, not a new extension. -/
theorem val_comp_mappedFiniteCompositumInclusion :
    ((adjoin K ((F.map e : IntermediateField k Ω) : Set Ω)).val.restrictScalars k).comp
      (mappedFiniteCompositumInclusion K F e) = e.comp F.val := by
  ext x
  rfl

/-- The original base-field maps commute through the same source-field inclusion. -/
theorem mappedFiniteCompositumInclusion_comp_algebraMap :
    (mappedFiniteCompositumInclusion K F e).toRingHom.comp (algebraMap k F) =
      algebraMap k (adjoin K ((F.map e : IntermediateField k Ω) : Set Ω)) := by
  exact RingHom.ext fun x => (mappedFiniteCompositumInclusion K F e).commutes x

end IntermediateField
