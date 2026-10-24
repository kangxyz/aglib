/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

/-!
# Irreducible components of a locally Noetherian space

Let `X` be a topological space in which every point has a Noetherian neighbourhood (a locally
Noetherian space, Stacks Project, Tag 0051). This module proves:

* the irreducible components of `X` form a locally finite family
  (`locallyFinite_irreducibleComponents_of_forall_exists_noetherianSpace`): a Noetherian open
  neighbourhood `V` of a point meets only finitely many components, because `Z ↦ Z ∩ V` sends the
  components meeting `V` injectively to irreducible components of `V` (Mathlib's
  `preimage_mem_irreducibleComponents`, and `Z` is the closure of `Z ∩ V`), and `V` has finitely
  many (Mathlib's `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`);
* hence every union of irreducible components is closed
  (`isClosed_sUnion_of_subset_irreducibleComponents_of_forall_exists_noetherianSpace`);
* **a homogeneity criterion for irreducibility**
  (`irreducibleSpace_of_forall_exists_noetherianSpace_of_forall_exists_homeomorph_closedPoints`):
  if moreover `X` is quasi-sober, Jacobson (closed points are dense in every closed subset) and
  connected, and its homeomorphisms act transitively on its closed points, then `X` is
  irreducible.

The criterion is the topological core of the irreducibility of the identity component of a group
scheme locally of finite type over an algebraically closed field (Stacks, Tag 0B7Q), where the
homeomorphisms are translations by rational points. Its proof runs as follows. For an irreducible
component `Z`, the union `W` of the other components is closed and misses the generic point of
`Z`, so the open set `X \ W` contains a closed point (Jacobson), which lies in no component other
than `Z`. Transporting by homeomorphisms, every closed point lies in exactly one component. Two
distinct components would meet in a nonempty closed set, which contains a closed point; so the
components are pairwise disjoint. Then the complement `W` of `Z` is closed, `Z` is open and
closed, and `Z` is all of the connected space `X`. This avoids the reduced subgroup schemes of
Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Lemma 5.1(3), p. 37 (`(G⁰)_red`, with generic
smoothness), and of Stacks 0B7Q (the reduced irreducible component through the identity).
-/

@[expose] public section

open Set Filter Topology TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- **The irreducible components of a locally Noetherian space are locally finite**: if every
point has a Noetherian neighbourhood, then every point has a neighbourhood meeting only finitely
many irreducible components. -/
theorem locallyFinite_irreducibleComponents_of_forall_exists_noetherianSpace
    (h : ∀ x : X, ∃ U ∈ 𝓝 x, NoetherianSpace U) :
    LocallyFinite (fun Z : irreducibleComponents X => (Z : Set X)) := by
  intro x
  obtain ⟨U, hU, hUN⟩ := h x
  refine ⟨interior U, interior_mem_nhds.mpr hU, ?_⟩
  have hVN : NoetherianSpace (interior U) :=
    (noetherianSpace_set_iff _).mpr fun t ht =>
      (noetherianSpace_set_iff U).mp hUN t (ht.trans interior_subset)
  have hV : IsOpen (interior U) := isOpen_interior
  refine Set.Finite.of_finite_image
    (f := fun Z : irreducibleComponents X => ((↑) : interior U → X) ⁻¹' (Z : Set X))
    (NoetherianSpace.finite_irreducibleComponents.subset ?_) ?_
  · rintro _ ⟨Z, hZ, rfl⟩
    exact preimage_mem_irreducibleComponents Z.2 hV.isOpenEmbedding_subtypeVal
      (by rw [Subtype.range_coe]; exact hZ)
  · intro Z₁ hZ₁ Z₂ hZ₂ heq
    have heq' : interior U ∩ (Z₁ : Set X) = interior U ∩ (Z₂ : Set X) :=
      Subtype.preimage_coe_eq_preimage_coe_iff.mp heq
    have key : ∀ Z₁ Z₂ : irreducibleComponents X, ((Z₁ : Set X) ∩ interior U).Nonempty →
        interior U ∩ (Z₁ : Set X) = interior U ∩ (Z₂ : Set X) → (Z₁ : Set X) ⊆ Z₂ := by
      intro Z₁ Z₂ hZ₁ heq
      refine (subset_closure_inter_of_isPreirreducible_of_isOpen Z₁.2.1.2 hV hZ₁).trans ?_
      rw [inter_comm, heq, (isClosed_of_mem_irreducibleComponents _ Z₂.2).closure_subset_iff]
      exact inter_subset_right
    exact Subtype.ext ((key Z₁ Z₂ hZ₁ heq').antisymm (key Z₂ Z₁ hZ₂ heq'.symm))

/-- **Every union of irreducible components of a locally Noetherian space is closed.** -/
theorem isClosed_sUnion_of_subset_irreducibleComponents_of_forall_exists_noetherianSpace
    (h : ∀ x : X, ∃ U ∈ 𝓝 x, NoetherianSpace U) {S : Set (Set X)}
    (hS : S ⊆ irreducibleComponents X) : IsClosed (⋃₀ S) := by
  have hlf : LocallyFinite (fun Z : S => (Z : Set X)) :=
    (locallyFinite_irreducibleComponents_of_forall_exists_noetherianSpace h).comp_injective
      (g := fun Z : S => (⟨Z, hS Z.2⟩ : irreducibleComponents X))
      fun Z₁ Z₂ e => by
        have h := congrArg (fun W : irreducibleComponents X => (W : Set X)) e
        exact Subtype.ext h
  rw [sUnion_eq_iUnion]
  exact hlf.isClosed_iUnion fun Z => isClosed_of_mem_irreducibleComponents _ (hS Z.2)

/-- In a quasi-sober space, an irreducible component is not covered by the other components: its
generic point lies in no other component. -/
theorem genericPoint_notMem_sUnion_irreducibleComponents_diff [QuasiSober X] {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) :
    hZ.1.genericPoint ∉ ⋃₀ (irreducibleComponents X \ {Z}) := by
  rintro ⟨Z', ⟨hZ', hZ'Z⟩, hξ⟩
  have hsub : Z ⊆ Z' :=
    ((hZ.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ hZ)).mem_closed_set_iff
        (isClosed_of_mem_irreducibleComponents _ hZ')).mp hξ
  exact hZ'Z (mem_singleton_iff.mpr ((hZ.2 hZ'.1 hsub).antisymm hsub))

/-- **Homogeneity criterion for irreducibility.** Let `X` be a nonempty connected, quasi-sober,
Jacobson space in which every point has a Noetherian neighbourhood. If for any two closed points
`x`, `y` there is a homeomorphism of `X` sending `x` to `y`, then `X` is irreducible. -/
theorem irreducibleSpace_of_forall_exists_noetherianSpace_of_forall_exists_homeomorph_closedPoints
    [QuasiSober X] [JacobsonSpace X] [ConnectedSpace X] (hN : ∀ x : X, ∃ U ∈ 𝓝 x, NoetherianSpace U)
    (hT : ∀ x ∈ closedPoints X, ∀ y ∈ closedPoints X, ∃ φ : X ≃ₜ X, φ x = y) :
    IrreducibleSpace X := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  set Z := irreducibleComponent x₀
  have hZ : Z ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x₀
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents _ hZ
  set W := ⋃₀ (irreducibleComponents X \ {Z})
  have hW : IsClosed W :=
    isClosed_sUnion_of_subset_irreducibleComponents_of_forall_exists_noetherianSpace hN sdiff_subset
  -- A closed point `c` lying in no component other than `Z`.
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints
    ⟨_, genericPoint_notMem_sUnion_irreducibleComponents_diff hZ⟩ hW.isOpen_compl.isLocallyClosed
  have hcZ : ∀ Z' ∈ irreducibleComponents X, c ∈ Z' → Z' = Z := fun Z' hZ' hcZ' => by
    by_contra hne
    exact hcW ⟨Z', ⟨hZ', hne⟩, hcZ'⟩
  -- Every closed point lies in exactly one component.
  have huniq : ∀ y ∈ closedPoints X, ∀ Z₁ ∈ irreducibleComponents X,
      ∀ Z₂ ∈ irreducibleComponents X, y ∈ Z₁ → y ∈ Z₂ → Z₁ = Z₂ := by
    intro y hy Z₁ hZ₁ Z₂ hZ₂ hy₁ hy₂
    obtain ⟨φ, hφ⟩ := hT c hc y hy
    have hpre : ∀ Z' ∈ irreducibleComponents X, y ∈ Z' → φ ⁻¹' Z' = Z := fun Z' hZ' hyZ' =>
      hcZ _ (preimage_mem_irreducibleComponents hZ' φ.isOpenEmbedding
        (by rw [φ.surjective.range_eq, inter_univ]; exact ⟨y, hyZ'⟩))
        (by rw [mem_preimage, hφ]; exact hyZ')
    exact preimage_injective.mpr φ.surjective ((hpre Z₁ hZ₁ hy₁).trans (hpre Z₂ hZ₂ hy₂).symm)
  -- Distinct components are disjoint.
  have hdisj : ∀ Z₁ ∈ irreducibleComponents X, ∀ Z₂ ∈ irreducibleComponents X,
      (Z₁ ∩ Z₂).Nonempty → Z₁ = Z₂ := by
    intro Z₁ hZ₁ Z₂ hZ₂ hne
    obtain ⟨y, ⟨hy₁, hy₂⟩, hy⟩ := nonempty_inter_closedPoints hne
      ((isClosed_of_mem_irreducibleComponents _ hZ₁).inter
        (isClosed_of_mem_irreducibleComponents _ hZ₂)).isLocallyClosed
    exact huniq y hy Z₁ hZ₁ Z₂ hZ₂ hy₁ hy₂
  -- The complement of `Z` is the closed set `W`, so `Z` is open and closed.
  have hcompl : Zᶜ = W := by
    ext y
    refine ⟨fun hy => ?_, ?_⟩
    · obtain ⟨Z', hZ', hyZ'⟩ := mem_sUnion.mp
        (show y ∈ ⋃₀ irreducibleComponents X by rw [sUnion_irreducibleComponents]; trivial)
      exact ⟨Z', ⟨hZ', fun e => hy ((mem_singleton_iff.mp e) ▸ hyZ')⟩, hyZ'⟩
    · rintro ⟨Z', ⟨hZ', hZ'Z⟩, hyZ'⟩ hyZ
      exact hZ'Z (mem_singleton_iff.mpr (hdisj Z' hZ' Z hZ ⟨y, hyZ', hyZ⟩))
  have hZo : IsOpen Z := by
    have h := hW.isOpen_compl
    rwa [← hcompl, compl_compl] at h
  have hZu : Z = univ := (isClopen_iff.mp ⟨hZc, hZo⟩).resolve_left
    (nonempty_iff_ne_empty.mp ⟨x₀, mem_irreducibleComponent⟩)
  have hu : IsIrreducible (univ : Set X) := hZu ▸ hZ.1
  exact (irreducibleSpace_def X).mpr hu
