/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Connected.Clopen

/-!
# Domain stalks and irreducible components

General component and connectedness lemmas extracted from
`R5Lab.AlgebraicGeometry.Geometrically.SmoothIntegral` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, including original lines 114–188.
The smooth relative-dimension-one domain and integrality endpoints are omitted.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- Two irreducible components through a point whose actual stalk is a
domain coincide. -/
lemma irreducibleComponents_eq_of_mem_of_isDomain_stalk
    {Z W : Set X} (hZ : Z ∈ irreducibleComponents X) (hW : W ∈ irreducibleComponents X)
    {x : X} (hxZ : x ∈ Z) (hxW : x ∈ W) [IsDomain (X.presheaf.stalk x)] : Z = W := by
  have hi : IsIrreducible (Set.range (X.fromSpecStalk x)) := by
    simpa only [Set.image_univ] using
      ((IrreducibleSpace.isIrreducible_univ _).image (X.fromSpecStalk x)
        (X.fromSpecStalk x).continuous.continuousOn)
  obtain ⟨C, hC, hSC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hi
  have aux (T : Set X) (hT : T ∈ irreducibleComponents X) (hxT : x ∈ T) : T = C := by
    have ht : hT.1.genericPoint ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact (hT.1.isGenericPoint_genericPoint
        (isClosed_of_mem_irreducibleComponents _ hT)).specializes hxT
    have hTC : T ⊆ C := by
      rw [← hT.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents _ hT)]
      exact closure_minimal (Set.singleton_subset_iff.mpr (hSC ht))
        (isClosed_of_mem_irreducibleComponents _ hC)
    exact Set.Subset.antisymm hTC (hT.2 hC.1 hTC)
  exact (aux Z hZ hxZ).trans (aux W hW hxW).symm

/-- With finitely many irreducible components and domain stalks, each
component is open. -/
lemma isOpen_irreducibleComponent_of_finite_of_isDomain_stalk
    (hfin : (irreducibleComponents X).Finite) [∀ x : X, IsDomain (X.presheaf.stalk x)]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) : IsOpen Z := by
  classical
  have hcompl : Zᶜ = ⋃₀ (irreducibleComponents X \ {Z}) := by
    ext y
    constructor
    · intro hy
      refine Set.mem_sUnion.mpr ⟨irreducibleComponent y, ?_, mem_irreducibleComponent⟩
      refine ⟨irreducibleComponent_mem_irreducibleComponents y, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro e
      exact hy (e ▸ mem_irreducibleComponent)
    · rintro ⟨W, ⟨hW, hWZ⟩, hyW⟩ hyZ
      exact hWZ (Set.mem_singleton_iff.mpr
        (irreducibleComponents_eq_of_mem_of_isDomain_stalk hW hZ hyW hyZ))
  rw [← isClosed_compl_iff, hcompl, Set.sUnion_eq_biUnion]
  exact hfin.sdiff.isClosed_biUnion fun W hW ↦
    isClosed_of_mem_irreducibleComponents _ hW.1

/-- Local Noetherianity and domain stalks make each irreducible component
open. -/
lemma isOpen_irreducibleComponent_of_isLocallyNoetherian_of_isDomain_stalk
    [IsLocallyNoetherian X] [∀ x : X, IsDomain (X.presheaf.stalk x)]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) : IsOpen Z := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  have : IsLocallyNoetherian (X.affineCover.X i) :=
    isLocallyNoetherian_of_isOpenImmersion (X.affineCover.f i)
  have : IsNoetherian (X.affineCover.X i) := ⟨⟩
  have (y : X.affineCover.X i) : IsDomain ((X.affineCover.X i).presheaf.stalk y) := by
    let e := (asIso ((X.affineCover.f i).stalkMap y)).commRingCatIsoToRingEquiv
    exact Function.Injective.isDomain e.symm.toRingHom e.symm.injective
  have hc : (X.affineCover.f i) ⁻¹' Z ∈ irreducibleComponents (X.affineCover.X i) :=
    preimage_mem_irreducibleComponents hZ (X.affineCover.f i).isOpenEmbedding
      ⟨_, hx, y, rfl⟩
  have hop := isOpen_irreducibleComponent_of_finite_of_isDomain_stalk
    (finite_irreducibleComponents_of_isNoetherian) hc
  refine ⟨(X.affineCover.f i) '' ((X.affineCover.f i) ⁻¹' Z),
    Set.image_preimage_subset _ _, (X.affineCover.f i).isOpenEmbedding.isOpenMap _ hop, y, hx, rfl⟩

/-- A connected locally Noetherian scheme with domain stalks is
irreducible. -/
lemma irreducibleSpace_of_connected_of_isLocallyNoetherian_of_isDomain_stalk
    [ConnectedSpace X] [IsLocallyNoetherian X]
    [∀ x : X, IsDomain (X.presheaf.stalk x)] : IrreducibleSpace X := by
  let x : X := Classical.choice inferInstance
  have hZ := irreducibleComponent_mem_irreducibleComponents x
  have hc : IsClopen (irreducibleComponent x) :=
    ⟨isClosed_of_mem_irreducibleComponents _ hZ,
      isOpen_irreducibleComponent_of_isLocallyNoetherian_of_isDomain_stalk hZ⟩
  have he := hc.eq_univ hZ.1.nonempty
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set X)
  rw [← he]
  exact hZ.1

end AlgebraicGeometry.Scheme
