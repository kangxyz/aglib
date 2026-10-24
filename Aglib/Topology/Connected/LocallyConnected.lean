/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.NoetherianSpace

/-!
# Locally Noetherian spaces are locally connected

A topological space in which every point has a Noetherian neighbourhood is locally connected
(`locallyConnectedSpace_of_forall_exists_noetherianSpace`; Stacks Project, Tag 04MF, where such a
space is called locally Noetherian, Tag 0051). In particular every Noetherian space is locally
connected (the instance `TopologicalSpace.NoetherianSpace.locallyConnectedSpace`), so its
connected components are open.

The proof is that of Stacks 04MF. In a Noetherian space the irreducible components are finitely
many and closed. The complement of the union of the components that do not contain `x` is an open
neighbourhood of `x`, and it lies in the union of the components through `x`, which is connected
(`TopologicalSpace.NoetherianSpace.isOpen_connectedComponent`). For a point with a Noetherian
neighbourhood `U` and any neighbourhood `V`, the interior of `U ∩ V` is an open Noetherian
subspace, and its connected component through the point is the required connected neighbourhood.
No separation axiom is assumed.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

namespace TopologicalSpace.NoetherianSpace

/-- **Connected components of a Noetherian space are open.** -/
theorem isOpen_connectedComponent [NoetherianSpace X] (x : X) :
    IsOpen (connectedComponent x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [connectedComponent_eq hy]
  have hfin : {Z ∈ irreducibleComponents X | y ∉ Z}.Finite :=
    NoetherianSpace.finite_irreducibleComponents.subset fun Z hZ => hZ.1
  have hclosed : IsClosed (⋃₀ {Z ∈ irreducibleComponents X | y ∉ Z}) :=
    hfin.isClosed_sUnion fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  refine Filter.mem_of_superset (hclosed.isOpen_compl.mem_nhds ?_) ?_
  · rintro ⟨Z, ⟨-, hyZ⟩, hy'⟩
    exact hyZ hy'
  · intro w hw
    have hw' : w ∈ ⋃₀ irreducibleComponents X := by
      rw [sUnion_irreducibleComponents]
      exact mem_univ w
    obtain ⟨Z, hZ, hwZ⟩ := hw'
    have hyZ : y ∈ Z := by
      by_contra h
      exact hw ⟨Z, ⟨hZ, h⟩, hwZ⟩
    exact hZ.1.isConnected.isPreconnected.subset_connectedComponent hyZ hwZ

end TopologicalSpace.NoetherianSpace

/-- **A space in which every point has a Noetherian neighbourhood is locally connected**
(Stacks 04MF). -/
theorem locallyConnectedSpace_of_forall_exists_noetherianSpace
    (h : ∀ x : X, ∃ U ∈ 𝓝 x, NoetherianSpace U) : LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x V hV
  obtain ⟨U, hU, hUN⟩ := h x
  have hxW : x ∈ interior (U ∩ V) := mem_interior_iff_mem_nhds.mpr (inter_mem hU hV)
  have hWU : interior (U ∩ V) ⊆ U := interior_subset.trans inter_subset_left
  have hWN : NoetherianSpace (interior (U ∩ V)) :=
    (noetherianSpace_set_iff _).mpr fun t ht => (noetherianSpace_set_iff U).mp hUN t (ht.trans hWU)
  refine ⟨connectedComponentIn (interior (U ∩ V)) x, ?_, isPreconnected_connectedComponentIn,
    (connectedComponentIn_subset _ _).trans (interior_subset.trans inter_subset_right)⟩
  rw [connectedComponentIn_eq_image hxW]
  exact (isOpen_interior.isOpenMap_subtype_val _
    (NoetherianSpace.isOpen_connectedComponent _)).mem_nhds
    ⟨⟨x, hxW⟩, mem_connectedComponent, rfl⟩

/-- **A Noetherian space is locally connected.** -/
instance (priority := 100) TopologicalSpace.NoetherianSpace.locallyConnectedSpace
    [NoetherianSpace X] : LocallyConnectedSpace X :=
  locallyConnectedSpace_of_forall_exists_noetherianSpace fun _ => ⟨univ, univ_mem, inferInstance⟩
