/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Clopen

/-!
# Clopen descent along a map with dense range

Open local positive and negative pieces whose inverse images have disjoint membership
cannot intersect: density detects any nonempty open intersection. If those pieces cover
the target, their positive union is clopen and has exactly the prescribed inverse image.
Neither a topology on the source nor continuity of the map is required.
-/

@[expose] public section

open Set

variable {X Y ι : Type*} [TopologicalSpace X] {g : Y → X}

/-- Open positive and negative pieces covering the target descend a subset along a map
with dense range. No compatibility on overlaps needs to be supplied. -/
theorem DenseRange.isClopen_iUnion_of_preimage_subset (hg : DenseRange g)
    {A B : ι → Set X} {S : Set Y}
    (hAopen : ∀ i, IsOpen (A i)) (hBopen : ∀ i, IsOpen (B i))
    (hcover : ∀ x, ∃ i, x ∈ A i ∨ x ∈ B i)
    (hA : ∀ i, g ⁻¹' A i ⊆ S) (hB : ∀ i, g ⁻¹' B i ⊆ Sᶜ) :
    IsClopen (⋃ i, A i) ∧ g ⁻¹' (⋃ i, A i) = S := by
  have hdisj (i j : ι) : Disjoint (A i) (B j) := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    obtain ⟨y, hyA, hyB⟩ :=
      hg.exists_mem_open ((hAopen i).inter (hBopen j)) ⟨x, hxA, hxB⟩
    exact hB j hyB (hA i hyA)
  have hcompl : (⋃ i, A i)ᶜ = ⋃ i, B i := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi | hi⟩ := hcover x
      · exact False.elim (hx (Set.mem_iUnion.mpr ⟨i, hi⟩))
      · exact Set.mem_iUnion.mpr ⟨i, hi⟩
    · intro hxB hxA
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxA
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxB
      exact Set.disjoint_left.mp (hdisj i j) hi hj
  refine ⟨⟨?_, isOpen_iUnion hAopen⟩, ?_⟩
  · rw [← isOpen_compl_iff, hcompl]
    exact isOpen_iUnion hBopen
  · ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      exact hA i hi
    · intro hy
      obtain ⟨i, hi | hi⟩ := hcover (g y)
      · exact Set.mem_iUnion.mpr ⟨i, hi⟩
      · exact False.elim (hB i hi hy)

/-- A clopen subset is uniquely determined by its inverse image under a map with dense
range, without any topology or continuity assumption on the source. -/
theorem DenseRange.eq_of_isClopen_preimage_eq (hg : DenseRange g)
    {s t : Set X} (hs : IsClopen s) (ht : IsClopen t)
    (h : g ⁻¹' s = g ⁻¹' t) : s = t := by
  have hsub {u v : Set X} (hu : IsOpen u) (hv : IsClosed v)
      (huv : g ⁻¹' u ⊆ g ⁻¹' v) : u ⊆ v := by
    intro x hx
    by_contra hxv
    obtain ⟨y, hyu, hyv⟩ :=
      hg.exists_mem_open (hu.inter hv.isOpen_compl) ⟨x, hx, hxv⟩
    exact hyv (huv hyu)
  exact Set.Subset.antisymm (hsub hs.isOpen ht.isClosed h.subset)
    (hsub ht.isOpen hs.isClosed h.symm.subset)
