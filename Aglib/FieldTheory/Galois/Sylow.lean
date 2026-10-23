/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Sylow

/-! # Sylow fixed fields in finite Galois extensions

The native fixed field of an actual Sylow subgroup has prime-to-p degree over
the base, and the remaining Galois extension has a p-group as its Galois group.
-/

@[expose] public noncomputable section

namespace IntermediateField

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] {p : ℕ} [Fact p.Prime]

/-- The actual Sylow fixed field has degree prime to p over the base field. -/
theorem finrank_fixedField_sylow_coprime (P : Sylow p (L ≃ₐ[K] L)) :
    (Module.finrank K (fixedField (P : Subgroup (L ≃ₐ[K] L)))).Coprime p := by
  rw [finrank_eq_fixingSubgroup_index, fixingSubgroup_fixedField]
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr P.not_dvd_index).symm

omit [IsGalois K L] [Fact p.Prime] in
/-- The remaining extension over the literal Sylow fixed field has p-group
Galois group, through the native subgroup-to-automorphism equivalence. -/
theorem isPGroup_gal_fixedField_sylow (P : Sylow p (L ≃ₐ[K] L)) :
    IsPGroup p (L ≃ₐ[fixedField (P : Subgroup (L ≃ₐ[K] L))] L) :=
  P.isPGroup'.of_equiv (subgroupEquivAlgEquiv (P : Subgroup (L ≃ₐ[K] L)))

end IntermediateField
