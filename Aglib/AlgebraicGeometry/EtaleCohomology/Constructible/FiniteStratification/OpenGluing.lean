/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.Partitions
public import Mathlib.Data.Fin.Tuple.Basic

/-! # Gluing actual partitions over finite retrocompact open covers

A finite cover by retrocompact opens carries actual local finite partitions.
Removing the preceding opens from each local stratum gives an actual global
finite locally closed partition. The strata are literal scheme pullbacks along
the reduced closed complements, with their original maps to the local strata.
No compactness, quasi-separatedness, or Noetherian hypothesis is imposed on
the ambient scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteLocallyClosedPartition

universe u v

variable {X : Scheme.{u}}

/-- Local actual partitions glue over a finite ordered retrocompact open
cover. Each resulting stratum retains its original map to a local stratum. -/
theorem exists_glue_open_cover_fin {n : ℕ} (U : Fin n → X.Opens)
    (hretro : ∀ i, IsRetrocompact (U i : Set X))
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (p : ∀ i, FiniteLocallyClosedPartition (U i).toScheme) :
    ∃ q : FiniteLocallyClosedPartition X,
      ∀ k, ∃ i j, ∃ a : q.stratum k ⟶ (p i).stratum j,
        a ≫ (p i).inclusion j ≫ (U i).ι = q.inclusion k := by
  classical
  let V (i : Fin n) : X.Opens := ⨆ k : {k : Fin n // k < i}, U k.val
  have hVmem (i : Fin n) (x : X) : x ∈ V i ↔ ∃ k, k < i ∧ x ∈ U k := by
    change x ∈ (⨆ k : {k : Fin n // k < i}, U k.val) ↔ _
    rw [TopologicalSpace.Opens.mem_iSup]
    constructor
    · rintro ⟨⟨k, hk⟩, hx⟩
      exact ⟨k, hk, hx⟩
    · rintro ⟨k, hk, hx⟩
      exact ⟨⟨k, hk⟩, hx⟩
  have hV (i : Fin n) : Topology.IsConstructible (V i : Set X) := by
    change Topology.IsConstructible
      ((⨆ k : {k : Fin n // k < i}, U k.val : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_iSup]
    exact Topology.IsConstructible.iUnion fun k =>
      (hretro k.val).isConstructible (U k.val).isOpen
  let I (i : Fin n) := IdealSheafData.vanishingIdeal (V i).compl
  let c (i : Fin n) : (I i).subscheme ⟶ X := (I i).subschemeι
  have hc (i : Fin n) : Set.range (c i) = (V i : Set X)ᶜ :=
    (IdealSheafData.range_subschemeι (I i)).trans
      (IdealSheafData.coe_support_vanishingIdeal _)
  let a : ∀ ij : Σ i, Fin (p i).count, (p ij.1).stratum ij.2 ⟶ X :=
    fun ij => (p ij.1).inclusion ij.2 ≫ (U ij.1).ι
  have ha (ij : Σ i, Fin (p i).count) :
      Topology.IsConstructible (Set.range (a ij)) := by
    change Topology.IsConstructible
      (Set.range ((U ij.1).ι ∘ (p ij.1).inclusion ij.2))
    rw [Set.range_comp]
    apply ((p ij.1).constructible_range ij.2).image_of_isOpenEmbedding
      (U ij.1).ι.isOpenEmbedding
    rw [Scheme.Opens.range_ι]
    exact hretro ij.1
  have ha_subset (ij : Σ i, Fin (p i).count) : Set.range (a ij) ⊆ U ij.1 := by
    rintro x ⟨y, rfl⟩
    exact ((p ij.1).inclusion ij.2 y).property
  let S (ij : Σ i, Fin (p i).count) : Scheme.{u} := pullback (a ij) (c ij.1)
  let f (ij : Σ i, Fin (p i).count) : S ij ⟶ X :=
    pullback.fst (a ij) (c ij.1) ≫ a ij
  have hf (ij : Σ i, Fin (p i).count) : IsImmersion (f ij) := by
    have : IsImmersion (a ij) := by
      dsimp only [a]
      have := (p ij.1).immersion ij.2
      infer_instance
    have : IsClosedImmersion (c ij.1) := by
      dsimp only [c]
      infer_instance
    dsimp only [f]
    infer_instance
  have hrange (ij : Σ i, Fin (p i).count) :
      Set.range (f ij) = Set.range (a ij) ∩ (V ij.1 : Set X)ᶜ := by
    change Set.range (pullback.fst (a ij) (c ij.1) ≫ a ij) = _
    rw [Scheme.Pullback.range_fst_comp, hc]
  have hconstruct (ij : Σ i, Fin (p i).count) :
      Topology.IsConstructible (Set.range (f ij)) := by
    rw [hrange]
    exact (ha ij).inter (hV ij.1).compl
  have hdisjoint : Pairwise fun ij kl => Disjoint (Set.range (f ij)) (Set.range (f kl)) := by
    rintro ⟨i, j⟩ ⟨k, l⟩ hne
    apply Set.disjoint_left.mpr
    intro x hxi hxk
    rw [hrange] at hxi hxk
    by_cases hik : i = k
    · subst k
      have hjl : j ≠ l := fun h => hne (by subst l; rfl)
      obtain ⟨y, hy⟩ := hxi.1
      obtain ⟨z, hz⟩ := hxk.1
      have heq : (p i).inclusion j y = (p i).inclusion l z :=
        (U i).ι.isOpenEmbedding.injective (hy.trans hz.symm)
      exact Set.disjoint_left.mp ((p i).disjoint hjl) ⟨y, rfl⟩ ⟨z, heq.symm⟩
    · rcases lt_or_gt_of_ne hik with hik | hki
      · exact hxk.2 ((hVmem k x).mpr ⟨i, hik, ha_subset ⟨i, j⟩ hxi.1⟩)
      · exact hxi.2 ((hVmem i x).mpr ⟨k, hki, ha_subset ⟨k, l⟩ hxk.1⟩)
  have hcoverage : ∀ x : X, ∃ ij, ∃ y : S ij, f ij y = x := by
    intro x
    let i := Fin.find (fun i => x ∈ U i) (hcover x)
    have hi : x ∈ U i := Fin.find_spec (hcover x)
    have hxV : x ∉ V i := by
      intro hx
      obtain ⟨k, hki, hxk⟩ := (hVmem i x).mp hx
      exact Fin.find_min (hcover x) hki hxk
    obtain ⟨j, y, hy⟩ := (p i).covers ⟨x, hi⟩
    have hy' : a ⟨i, j⟩ y = x := congrArg (U i).ι hy
    have hxc : x ∈ Set.range (c i) := by
      rw [hc]
      exact hxV
    obtain ⟨z, hz⟩ := hxc
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := a ⟨i, j⟩) (g := c i) y z (hy'.trans hz.symm)
    refine ⟨⟨i, j⟩, w, ?_⟩
    change a ⟨i, j⟩ (pullback.fst (a ⟨i, j⟩) (c i) w) = x
    rw [hw]
    exact hy'
  let q := ofFintype S f hf hconstruct hdisjoint hcoverage
  refine ⟨q, ?_⟩
  intro k
  let ij := (Fintype.equivFin (Σ i, Fin (p i).count)).symm k
  exact ⟨ij.1, ij.2, pullback.fst (a ij) (c ij.1), rfl⟩

/-- Actual partitions glue over an arbitrary finite retrocompact open cover.
Reindexing changes only labels, not the original local strata or their maps. -/
theorem exists_glue_open_cover {ι : Type v} [Finite ι] (U : ι → X.Opens)
    (hretro : ∀ i, IsRetrocompact (U i : Set X))
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (p : ∀ i, FiniteLocallyClosedPartition (U i).toScheme) :
    ∃ q : FiniteLocallyClosedPartition X,
      ∀ k, ∃ i j, ∃ a : q.stratum k ⟶ (p i).stratum j,
        a ≫ (p i).inclusion j ≫ (U i).ι = q.inclusion k := by
  classical
  let := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  obtain ⟨q, hq⟩ := exists_glue_open_cover_fin (fun i => U (e.symm i))
    (fun i => hretro (e.symm i))
    (by
      intro x
      obtain ⟨i, hi⟩ := hcover x
      exact ⟨e i, by simpa only [Equiv.symm_apply_apply] using hi⟩)
    (fun i => p (e.symm i))
  refine ⟨q, ?_⟩
  intro k
  obtain ⟨i, j, a, ha⟩ := hq k
  exact ⟨e.symm i, j, a, ha⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteLocallyClosedPartition
