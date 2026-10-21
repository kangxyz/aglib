/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-! # Differentials of actual field generators

Field generation suffices: the proof includes inverses and does not assume the
field is generated as a ring or algebra. The target is the displayed generated
field, not an unspecified larger ambient field.
-/

@[expose] public noncomputable section

namespace KaehlerDifferential

variable {k K ι : Type*} [Field k] [Field K] [Algebra k K]

/-- The differentials of a field-generating family span the differential module. -/
theorem span_range_D_of_adjoin_eq_top (x : ι → K)
    (hx : IntermediateField.adjoin k (Set.range x) = ⊤) :
    Submodule.span K (Set.range (fun i => D k K (x i))) = ⊤ := by
  apply top_unique
  rw [← span_range_derivation k K]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, rfl⟩
  have ha : a ∈ IntermediateField.adjoin k (Set.range x) := by
    rw [hx]
    trivial
  refine IntermediateField.adjoin_induction (F := k)
    (p := fun a _ => D k K a ∈ Submodule.span K (Set.range (fun i => D k K (x i))))
    ?_ ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  · intro r
    rw [Derivation.map_algebraMap]
    exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  · intro a _ ha
    rw [Derivation.leibniz_inv]
    exact Submodule.smul_mem _ _ ha
  · intro a b _ _ ha hb
    rw [Derivation.leibniz]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ ha)

end KaehlerDifferential
