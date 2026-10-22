/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps

/-! # Defect bounds under restriction of scalars

An extended-ideal bound implies the original ideal bound on the same linear
map with restricted scalars. This does not require faithful flatness.
-/

@[expose] public section
namespace LinearMap

/-- Restricting scalars preserves the original ideal bound on both defects. -/
theorem defectBounds_restrictScalars
    {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[S] N) (J : Ideal R)
    (hk : Ideal.map (algebraMap R S) J • f.ker = ⊥)
    (hc : Ideal.map (algebraMap R S) J • (⊤ : Submodule S N) ≤ f.range) :
    J • (f.restrictScalars R).ker = ⊥ ∧
      J • (⊤ : Submodule R N) ≤ (f.restrictScalars R).range := by
  constructor
  · apply le_antisymm _ bot_le
    apply Submodule.smul_le.mpr
    intro r hr x hx
    have hz := Submodule.smul_mem_smul
      (Ideal.mem_map_of_mem (algebraMap R S) hr) (show x ∈ f.ker from hx)
    rw [hk] at hz
    change r • x = 0
    simpa only [Submodule.mem_bot, algebraMap_smul] using hz
  · apply Submodule.smul_le.mpr
    intro r hr y _
    obtain ⟨x, hx⟩ := hc (Submodule.smul_mem_smul
      (Ideal.mem_map_of_mem (algebraMap R S) hr) (Submodule.mem_top : y ∈ ⊤))
    refine ⟨x, ?_⟩
    change f x = r • y
    simpa only [algebraMap_smul] using hx

end LinearMap
