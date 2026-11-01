/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober

/-!
# Krull dimension under closed surjections

A closed continuous surjection between sober spaces cannot increase Krull
dimension. Closed maps lift specializations; strict specialization chains
lift with the same length. No Noetherian or finite-dimensional hypothesis is
needed. The schematic-image dimension bound for proper Abel maps consumes
this topological result.
-/

@[expose] public noncomputable section

open Order TopologicalSpace

private theorem exists_ltSeries_lift {α β : Type*} [Preorder α] [Preorder β]
    (f : α → β) (hlift : Relation.Fibration (· < ·) (· < ·) f)
    (hsurj : Function.Surjective f) (p : LTSeries β) :
    ∃ q : LTSeries α, q.length = p.length ∧ f q.head = p.head := by
  induction p using RelSeries.inductionOn with
  | singleton b =>
    obtain ⟨a, rfl⟩ := hsurj b
    exact ⟨RelSeries.singleton _ a, rfl, rfl⟩
  | cons p b hb ih =>
    obtain ⟨q, hqlength, hqhead⟩ := ih
    obtain ⟨a, haq, hfa⟩ := hlift (show b < f q.head by rwa [hqhead])
    refine ⟨q.cons a haq, ?_, ?_⟩
    · simp only [RelSeries.cons_length, hqlength]
    · simpa only [RelSeries.head_cons] using hfa

private theorem krullDim_le_of_surjective_of_le_lifting
    {α β : Type*} [Preorder α] [Preorder β] (f : α → β) (hmono : Monotone f)
    (hlift : Relation.Fibration (· ≤ ·) (· ≤ ·) f) (hsurj : Function.Surjective f) :
    Order.krullDim β ≤ Order.krullDim α := by
  have hlt : Relation.Fibration (· < ·) (· < ·) f := by
    intro a b hb
    obtain ⟨a', ha', hfa'⟩ := hlift hb.le
    refine ⟨a', lt_of_le_not_ge ha' ?_, hfa'⟩
    intro haa'
    exact hb.not_ge (hfa' ▸ hmono haa')
  apply iSup_le
  intro p
  obtain ⟨q, hq, -⟩ := exists_ltSeries_lift f hlt hsurj p
  simpa only [hq] using q.length_le_krullDim

attribute [local instance] specializationOrder

namespace TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [QuasiSober X] [T0Space X] [QuasiSober Y] [T0Space Y]

/-- A continuous surjective map that lifts specializations cannot increase
topological Krull dimension, including empty and infinite-dimensional spaces. -/
theorem topologicalKrullDim_le_of_specializingMap_of_surjective
    (f : X → Y) (hf : Continuous f) (hsp : SpecializingMap f)
    (hsurj : Function.Surjective f) : topologicalKrullDim Y ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim, topologicalKrullDim,
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y)),
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  exact krullDim_le_of_surjective_of_le_lifting f hf.specialization_monotone hsp hsurj

/-- A closed continuous surjection between sober spaces cannot increase
topological Krull dimension. -/
theorem topologicalKrullDim_le_of_isClosedMap_of_surjective
    (f : X → Y) (hf : Continuous f) (hclosed : IsClosedMap f)
    (hsurj : Function.Surjective f) : topologicalKrullDim Y ≤ topologicalKrullDim X :=
  topologicalKrullDim_le_of_specializingMap_of_surjective f hf
    hclosed.specializingMap hsurj

end TopologicalSpace
