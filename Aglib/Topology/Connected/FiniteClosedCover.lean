/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Connected.Clopen

/-!
# Propagation through actual intersections of finite closed covers


Source: `R5Lab.Aglib.Topology.Connected.FiniteClosedCover`.
Packet SHA-256:
`27e522ba698bc24c39b03906af51f646e371cfef01dab6f55d8bc70d9c93ca0f`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
open Set TopologicalSpace
universe u v


/-- Induction over the ACTUAL irreducible components of a Noetherian normal
source of a closed surjection onto a connected space. The transition relation
is the actual intersection of component images, not a supplied graph. -/
theorem irreducibleComponentImageInduction
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [NoetherianSpace X] [ConnectedSpace Y] (q : X → Y)
    (hq : Function.Surjective q) (hclosed : IsClosedMap q)
    (hopen : ∀ C : irreducibleComponents X, IsOpen C.val)
    (P : irreducibleComponents X → Prop)
    (hstart : ∃ C, P C)
    (hstep : ∀ C D : irreducibleComponents X,
      (q '' C.val ∩ q '' D.val).Nonempty → P C → P D) : ∀ C, P C := by
  classical
  let : Finite (irreducibleComponents X) := NoetherianSpace.finite_irreducibleComponents.to_subtype
  let S : Set X := {x | ∃ C : irreducibleComponents X, P C ∧ x ∈ C.val}
  have hS : S = ⋃ C : {C : irreducibleComponents X // P C}, C.val.val := by
    ext x
    simp only [S, mem_ofPred_eq, mem_iUnion, Subtype.exists, exists_prop]
  have hSopen : IsOpen S := by
    rw [hS]
    exact isOpen_iUnion fun C => hopen C.val
  have hSclosed : IsClosed S := by
    rw [hS]
    exact isClosed_iUnion_of_finite fun C => isClosed_of_mem_irreducibleComponents _ C.val.property
  have hsaturated {x y : X} (hx : x ∈ S) (hxy : q x = q y) : y ∈ S := by
    obtain ⟨C, hC, hxC⟩ := hx
    let D : irreducibleComponents X := ⟨irreducibleComponent y,
      irreducibleComponent_mem_irreducibleComponents y⟩
    have hyD : y ∈ D.val := mem_irreducibleComponent
    exact ⟨D, hstep C D ⟨q x, ⟨x, hxC, rfl⟩, ⟨y, hyD, hxy.symm⟩⟩ hC, hyD⟩
  have hcomplement : (q '' S)ᶜ = q '' Sᶜ := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := hq y
      exact ⟨x, fun hx => hy ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩ ⟨z, hz, hzx⟩
      exact hx (hsaturated hz hzx)
  have hT : IsClopen (q '' S) := by
    refine ⟨hclosed S hSclosed, ?_⟩
    rw [← isClosed_compl_iff, hcomplement]
    exact hclosed _ hSopen.isClosed_compl
  have hTne : (q '' S).Nonempty := by
    obtain ⟨C, hC⟩ := hstart
    obtain ⟨x, hx⟩ := C.property.1.nonempty
    exact ⟨q x, x, ⟨C, hC, hx⟩, rfl⟩
  have hTuniv : q '' S = univ := hT.eq_univ hTne
  intro C
  obtain ⟨x, hx⟩ := C.property.1.nonempty
  have hqx : q x ∈ q '' S := by rw [hTuniv]; trivial
  obtain ⟨z, ⟨D, hD, hz⟩, hzx⟩ := hqx
  exact hstep D C ⟨q x, ⟨z, hz, hzx⟩, ⟨x, hx, rfl⟩⟩ hD

/-- Connectedness propagates through the actual intersections of any finite
nonempty closed cover. The sets and intersections are retained in the statement. -/
theorem finiteClosedCoverInduction {Y : Type u} [TopologicalSpace Y] [ConnectedSpace Y]
    {I : Type v} [Finite I] (s : I → Set Y)
    (hclosed : ∀ i, IsClosed (s i)) (hne : ∀ i, (s i).Nonempty)
    (hcover : ∀ y, ∃ i, y ∈ s i) (P : I → Prop)
    (hstart : ∃ i, P i)
    (hstep : ∀ i j, (s i ∩ s j).Nonempty → P i → P j) : ∀ i, P i := by
  classical
  let T : Set Y := ⋃ i : {i : I // P i}, s i.val
  have hTclosed : IsClosed T := isClosed_iUnion_of_finite fun i => hclosed i.val
  have hcomplement : Tᶜ = ⋃ i : {i : I // ¬ P i}, s i.val := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := hcover y
      refine Set.mem_iUnion.mpr ⟨⟨i, ?_⟩, hi⟩
      intro hP
      exact hy (Set.mem_iUnion.mpr ⟨⟨i, hP⟩, hi⟩)
    · rintro hy hTy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hTy
      exact i.property (hstep j.val i.val ⟨y, hj, hi⟩ j.property)
  have hT : IsClopen T := ⟨hTclosed, by
    rw [← isClosed_compl_iff, hcomplement]
    exact isClosed_iUnion_of_finite fun i => hclosed i.val⟩
  have hTne : T.Nonempty := by
    obtain ⟨i, hi⟩ := hstart
    obtain ⟨y, hy⟩ := hne i
    exact ⟨y, Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hy⟩⟩
  have hTuniv := hT.eq_univ hTne
  intro i
  obtain ⟨y, hy⟩ := hne i
  have hyT : y ∈ T := by rw [hTuniv]; trivial
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hyT
  exact hstep j.val i ⟨y, hj, hy⟩ j.property
