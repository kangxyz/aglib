/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Topology.Irreducible.LocallyFinite

/-!
# Irreducible components of a locally Noetherian space

The examples restate that the irreducible components of a space whose points have Noetherian
neighbourhoods are locally finite, that every union of components is closed, and the homogeneity
criterion for irreducibility, and guard the axioms.
-/

@[expose] public section

open Set Filter Topology TopologicalSpace

namespace AglibTest.IrreducibleLocallyFinite

variable {X : Type*} [TopologicalSpace X]

/-- The irreducible components of a locally Noetherian space are locally finite. -/
theorem locallyFinite (h : ∀ x : X, ∃ U ∈ 𝓝 x, NoetherianSpace U) :
    LocallyFinite (fun Z : irreducibleComponents X => (Z : Set X)) :=
  locallyFinite_irreducibleComponents_of_forall_exists_noetherianSpace h

/-- The union of the irreducible components not containing a given point is closed. -/
theorem isClosed_sUnion_not_mem (h : ∀ x : X, ∃ U ∈ 𝓝 x, NoetherianSpace U) (x : X) :
    IsClosed (⋃₀ {Z ∈ irreducibleComponents X | x ∉ Z}) :=
  isClosed_sUnion_of_subset_irreducibleComponents_of_forall_exists_noetherianSpace h fun _ hZ => hZ.1

/-- A Noetherian space satisfies the hypothesis with the whole space as neighbourhood. -/
example [NoetherianSpace X] {S : Set (Set X)} (hS : S ⊆ irreducibleComponents X) :
    IsClosed (⋃₀ S) :=
  isClosed_sUnion_of_subset_irreducibleComponents_of_forall_exists_noetherianSpace (fun _ => ⟨univ, univ_mem, inferInstance⟩) hS

/-- The homogeneity criterion: a connected, quasi-sober, Jacobson, locally Noetherian space whose
homeomorphisms act transitively on closed points is irreducible. -/
theorem irreducible [QuasiSober X] [JacobsonSpace X] [ConnectedSpace X]
    (hN : ∀ x : X, ∃ U ∈ 𝓝 x, NoetherianSpace U)
    (hT : ∀ x ∈ closedPoints X, ∀ y ∈ closedPoints X, ∃ φ : X ≃ₜ X, φ x = y) :
    IsIrreducible (univ : Set X) :=
  have := irreducibleSpace_of_forall_exists_noetherianSpace_of_forall_exists_homeomorph_closedPoints hN hT
  IrreducibleSpace.isIrreducible_univ X

/-- info: 'locallyFinite_irreducibleComponents_of_forall_exists_noetherianSpace' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms locallyFinite_irreducibleComponents_of_forall_exists_noetherianSpace

/-- info: 'isClosed_sUnion_of_subset_irreducibleComponents_of_forall_exists_noetherianSpace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms isClosed_sUnion_of_subset_irreducibleComponents_of_forall_exists_noetherianSpace

/-- info: 'genericPoint_notMem_sUnion_irreducibleComponents_diff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms genericPoint_notMem_sUnion_irreducibleComponents_diff

/-- info: 'irreducibleSpace_of_forall_exists_noetherianSpace_of_forall_exists_homeomorph_closedPoints' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms irreducibleSpace_of_forall_exists_noetherianSpace_of_forall_exists_homeomorph_closedPoints

end AglibTest.IrreducibleLocallyFinite
