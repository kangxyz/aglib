/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.JacobsonSpace

/-! # Open covers detected on closed points

An actual family of opens in a Jacobson space covers the whole space if it
covers every closed point. No constructibility of an independently defined
locus and no finiteness of the indexing family are required.
-/

@[expose] public section

universe u v

namespace TopologicalSpace

/-- A family of actual opens covering the closed points of a Jacobson space
covers every point of that same space. -/
theorem exists_mem_open_of_closedPoint_cover
    {X : Type u} [TopologicalSpace X] [JacobsonSpace X]
    {ι : Type v} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hclosed : ∀ x : X, IsClosed ({x} : Set X) → ∃ i, x ∈ U i)
    (x : X) : ∃ i, x ∈ U i := by
  classical
  by_contra hx
  have hx' : x ∈ (⋃ i, U i)ᶜ := by
    intro hxU
    exact hx (Set.mem_iUnion.mp hxU)
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
    (show (⋃ i, U i)ᶜ.Nonempty from ⟨x, hx'⟩)
    (isOpen_iUnion hU).isClosed_compl.isLocallyClosed
  obtain ⟨i, hi⟩ := hclosed z hzc
  exact hz (Set.mem_iUnion.mpr ⟨i, hi⟩)

end TopologicalSpace
