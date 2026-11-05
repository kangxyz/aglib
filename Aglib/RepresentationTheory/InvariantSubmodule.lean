/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants

/-! # Invariant submodules over arbitrary scalar rings

The usual invariant submodule does not require commutative scalars. This
construction keeps exactly its fixed vectors, and agrees with the existing
commutative construction without transporting the underlying module.
-/

@[expose] public noncomputable section

namespace Representation

variable {R G V : Type*} [Ring R] [Group G] [AddCommGroup V] [Module R V]

/-- The original fixed vectors, with their inherited left scalar action. -/
def invariantSubmodule (ρ : Representation R G V) : Submodule R V where
  carrier := Set.ofPred fun v => ∀ g : G, ρ g v = v
  zero_mem' g := by simp only [map_zero]
  add_mem' hv hw g := by simp only [hv g, hw g, map_add]
  smul_mem' r v hv g := by simp only [hv g, map_smulₛₗ, RingHom.id_apply]

@[simp]
theorem mem_invariantSubmodule (ρ : Representation R G V) (v : V) :
    v ∈ ρ.invariantSubmodule ↔ ∀ g : G, ρ g v = v := Iff.rfl

end Representation

namespace Representation

variable {R G V : Type*} [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- For commutative scalars these are literally the original invariants. -/
theorem invariantSubmodule_eq_invariants (ρ : Representation R G V) :
    ρ.invariantSubmodule = ρ.invariants := rfl

end Representation
