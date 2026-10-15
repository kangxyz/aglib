/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Closed subspaces avoiding generic points

Closed subspaces avoiding all component generic points lower topological
Krull dimension. The dimension comparison retains only QuasiSober; the
open-neighborhood lemma retains its stated Noetherian assumption. These are
topological statements with no sheaf, scheme or cohomology input.

Source: `R5Lab.CategoryTheory.Sheaves.NoetherianCohomology` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`. The three generic-point and closed-subspace
  dimension lemmas only.
-/

@[expose] public section

open Set Order TopologicalSpace Topology

namespace TopologicalSpace

universe u

/-- An open set missing a component generic point has an open neighborhood
of that generic point disjoint from it. -/
lemma genericPoint_exists_open_disjoint
    {X : Type u} [TopologicalSpace X] [NoetherianSpace X]
    (η : X) (hη : η ∈ genericPoints X) (U : Opens X) (hηU : η ∉ U) :
    ∃ W : Opens X, η ∈ W ∧ Disjoint U W := by
  obtain ⟨W, hWopen, ⟨x, hx⟩, hWC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (closure ({η} : Set X)) hη
  have hηW : η ∈ W :=
    (isGenericPoint_closure.mem_open_set_iff hWopen).2 ⟨x, hWC hx, hx⟩
  refine ⟨⟨W, hWopen⟩, hηW, ?_⟩
  have hCU : Disjoint (closure ({η} : Set X)) (U : Set X) :=
    isGenericPoint_closure.disjoint_iff U.isOpen |>.2 hηU
  exact Opens.coe_disjoint.1 (hCU.mono_left hWC).symm

/-- Every irreducible closed subset of a closed subspace avoiding the component
generic points is strictly contained in an ambient irreducible closed subset. -/
lemma exists_irreducibleCloseds_gt_of_avoids_genericPoints
    {X : Type u} [TopologicalSpace X] [QuasiSober X]
    (Z : Set X) (hZ : IsClosed Z) (hgeneric : Disjoint Z (genericPoints X))
    (S : IrreducibleCloseds Z) :
    ∃ T : IrreducibleCloseds X,
      IrreducibleCloseds.map Subtype.val continuous_subtype_val S < T := by
  let A := IrreducibleCloseds.map Subtype.val continuous_subtype_val S
  have hAZ : (A : Set X) ⊆ Z := by
    apply hZ.closure_subset_iff.2
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  obtain ⟨C, hC, hAC⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (A : Set X) A.isIrreducible
  let T : IrreducibleCloseds X :=
    ⟨C, hC.1, isClosed_of_mem_irreducibleComponents C hC⟩
  refine ⟨T, lt_of_le_not_ge hAC ?_⟩
  intro hCA
  let η := genericPoints.ofComponent ⟨C, hC⟩
  have hηC : (η : X) ∈ C := (genericPoints.isGenericPoint_ofComponent ⟨C, hC⟩).mem
  exact Set.disjoint_left.1 hgeneric (hAZ (hCA hηC)) η.property

/-- A closed subspace avoiding every ambient component generic point has
dimension at most `d` if the ambient dimension is at most `d + 1`.
No nonemptiness, separation, or Noetherian assumption is required. -/
lemma topologicalKrullDim_closed_le_of_avoids_genericPoints
    {X : Type u} [TopologicalSpace X] [QuasiSober X]
    (Z : Set X) (hZ : IsClosed Z) (hgeneric : Disjoint Z (genericPoints X))
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ)) :
    topologicalKrullDim Z ≤ (d : ℕ) := by
  change krullDim (IrreducibleCloseds Z) ≤ _
  refine iSup_le fun p => ?_
  let q := p.map (IrreducibleCloseds.map Subtype.val continuous_subtype_val)
    (IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal)
  obtain ⟨T, hT⟩ := exists_irreducibleCloseds_gt_of_avoids_genericPoints
    Z hZ hgeneric p.last
  have hqT : q.last < T := hT
  have hlength := (LTSeries.length_le_krullDim (q.snoc T hqT)).trans hdim
  have hlength' : p.length + 1 ≤ d + 1 := by
    simpa only [RelSeries.snoc_length, q, LTSeries.map_length, Nat.cast_le] using hlength
  exact Nat.cast_le.2 (Nat.le_of_succ_le_succ hlength')

end TopologicalSpace
