/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RepresentationTheory.Invariants

/-! # Invariant lifts along original equivariant surjections

The native averaging projection commutes with every original intertwining map.
When the group order is invertible, a surjection therefore lifts each invariant
target vector to an invariant source vector. No new representation model is used.
-/

@[expose] public noncomputable section

namespace Representation

universe r g v w

variable {R : Type r} [CommRing R] {G : Type g} [Group G] [Fintype G]
  [Invertible (Fintype.card G : R)]
  {V : Type v} [AddCommGroup V] [Module R V]
  {W : Type w} [AddCommGroup W] [Module R W]
  {ρ : Representation R G V} {σ : Representation R G W}

/-- The original intertwining map commutes with the existing averaging projection. -/
theorem IntertwiningMap.map_averageMap (f : IntertwiningMap ρ σ) (v : V) :
    f (ρ.averageMap v) = σ.averageMap (f v) := by
  let f' := IntertwiningMap.equivLinearMapAsModule ρ σ f
  exact congrArg σ.asModuleEquiv
    (f'.map_smul (GroupAlgebra.average R G) (ρ.asModuleEquiv.symm v))

/-- Every invariant vector has an invariant preimage under the unchanged
surjective intertwining map. The source and target module universes are independent. -/
theorem IntertwiningMap.exists_invariant_preimage (f : IntertwiningMap ρ σ)
    (hf : Function.Surjective f) {w : W} (hw : w ∈ σ.invariants) :
    ∃ v : V, v ∈ ρ.invariants ∧ f v = w := by
  obtain ⟨v, rfl⟩ := hf w
  refine ⟨ρ.averageMap v, ρ.averageMap_invariant v, ?_⟩
  exact (f.map_averageMap v).trans (σ.averageMap_id (f v) hw)

end Representation
