/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.KrullDimension

/-! # Dimension at most one from generic or closed points -/

@[expose] public noncomputable section

open Set TopologicalSpace Order

namespace TopologicalSpace

universe u

/-- In a sober space, generic-or-closed points force dimension at most one. -/
theorem topologicalKrullDim_le_one_of_generic_or_closed
    {X : Type u} [TopologicalSpace X] [QuasiSober X]
    (h : ∀ x : X, x ∈ genericPoints X ∨ IsClosed ({x} : Set X)) :
    topologicalKrullDim X ≤ 1 := by
  apply krullDim_le_one_iff.mpr
  intro Y
  let y := Y.2.genericPoint
  have hy : IsGenericPoint y (Y : Set X) := Y.2.isGenericPoint_genericPoint Y.3
  rcases h y with hg | hc
  · right
    change closure ({y} : Set X) ∈ irreducibleComponents X at hg
    rw [hy.def, irreducibleComponents_eq_maximals_closed] at hg
    intro Z hYZ
    exact hg.2 ⟨Z.3, Z.2⟩ hYZ
  · left
    have hY : (Y : Set X) = {y} := hy.def.symm.trans hc.closure_eq
    intro Z hZY
    obtain ⟨z, hz⟩ := Z.2.nonempty
    have hzy : z = y := by
      have hzY : z ∈ (Y : Set X) := hZY hz
      rwa [hY, mem_singleton_iff] at hzY
    intro x hx
    have hxy : x = y := by
      change x ∈ (Y : Set X) at hx
      rwa [hY, mem_singleton_iff] at hx
    exact hxy.symm ▸ (hzy ▸ hz)

end TopologicalSpace
