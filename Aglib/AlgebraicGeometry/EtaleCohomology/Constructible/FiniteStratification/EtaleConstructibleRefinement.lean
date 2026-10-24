/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.AffineEtale
public import Mathlib.Topology.Clopen

/-! # Clopen constructible refinements along affine etale maps

Over an arbitrary affine base, finitely many constructible subsets of an
actual affine etale source become clopen in the entire pulled-back source
on a finite locally closed partition. The structural maps on the same
partition are finite. The proof uses finite principal-open covers and
actual common refinements, without a Noetherian or reducedness hypothesis.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u v

namespace FiniteLocallyClosedPartition

variable {X Y : Scheme.{u}} {p q : FiniteLocallyClosedPartition X}

/-- The actual comparison of source pullbacks induced by an original
refinement map between strata. -/
def Refinement.pullbackMap (r : q.Refinement p) (f : Y ⟶ X) (i : Fin q.count) :
    pullback f (q.inclusion i) ⟶ pullback f (p.inclusion (r.indexMap i)) :=
  pullback.lift (pullback.fst f (q.inclusion i))
    (pullback.snd f (q.inclusion i) ≫ r.map i) (by
      rw [Category.assoc, r.comm, pullback.condition])

@[reassoc (attr := simp)]
theorem Refinement.pullbackMap_fst (r : q.Refinement p) (f : Y ⟶ X)
    (i : Fin q.count) :
    r.pullbackMap f i ≫ pullback.fst f (p.inclusion (r.indexMap i)) =
      pullback.fst f (q.inclusion i) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem Refinement.pullbackMap_snd (r : q.Refinement p) (f : Y ⟶ X)
    (i : Fin q.count) :
    r.pullbackMap f i ≫ pullback.snd f (p.inclusion (r.indexMap i)) =
      pullback.snd f (q.inclusion i) ≫ r.map i :=
  pullback.lift_snd _ _ _

/-- Finiteness survives an actual refinement, with no compactness
assumption on the refinement map. -/
theorem Refinement.isFinite_pullback_snd (r : q.Refinement p) (f : Y ⟶ X)
    (hp : ∀ i, IsFinite (pullback.snd f (p.inclusion i))) :
    ∀ i, IsFinite (pullback.snd f (q.inclusion i)) := by
  intro i
  rw [← r.comm i]
  apply (isFinite_pullback_snd_comp_iff f (p.inclusion (r.indexMap i)) (r.map i)).mpr
  have := hp (r.indexMap i)
  infer_instance

/-- An original subset remains clopen in the whole pulled-back source
when the base partition is actually refined. -/
theorem Refinement.isClopen_preimage (r : q.Refinement p) (f : Y ⟶ X) (s : Set Y)
    (hp : ∀ i, IsClopen ((pullback.fst f (p.inclusion i)) ⁻¹' s)) :
    ∀ i, IsClopen ((pullback.fst f (q.inclusion i)) ⁻¹' s) := by
  intro i
  have h := (hp (r.indexMap i)).preimage (r.pullbackMap f i).continuous
  simpa only [← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
    Refinement.pullbackMap_fst] using h

end FiniteLocallyClosedPartition

private theorem exists_common_clopen_partition_fin {X Y : Scheme.{u}}
    (f : Y ⟶ X) (n : ℕ) (s : Fin n → Set Y)
    (hs : ∀ i, ∃ p : FiniteLocallyClosedPartition X,
      ∀ k, IsClopen ((pullback.fst f (p.inclusion k)) ⁻¹' s i)) :
    ∃ p : FiniteLocallyClosedPartition X,
      ∀ i k, IsClopen ((pullback.fst f (p.inclusion k)) ⁻¹' s i) := by
  induction n with
  | zero => exact ⟨.singleton X, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih (fun i => s i.succ) (fun i => hs i.succ)
    obtain ⟨q, hq⟩ := hs 0
    refine ⟨p.intersection q, ?_⟩
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact (p.intersectionRefinesRight q).isClopen_preimage f (s 0) hq
    · exact (p.intersectionRefinesLeft q).isClopen_preimage f (s k.succ) (hp k)

/-- Finitely many original subsets with clopen-refinement partitions have
one actual common partition. The original subsets, not their images on
the base, are retained. -/
theorem exists_common_clopen_partition {X Y : Scheme.{u}} (f : Y ⟶ X)
    {ι : Type v} [Finite ι] (s : ι → Set Y)
    (hs : ∀ i, ∃ p : FiniteLocallyClosedPartition X,
      ∀ k, IsClopen ((pullback.fst f (p.inclusion k)) ⁻¹' s i)) :
    ∃ p : FiniteLocallyClosedPartition X,
      ∀ i k, IsClopen ((pullback.fst f (p.inclusion k)) ⁻¹' s i) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨p, hp⟩ := exists_common_clopen_partition_fin f (Fintype.card ι)
    (fun i => s ((Fintype.equivFin ι).symm i))
    (fun i => hs ((Fintype.equivFin ι).symm i))
  refine ⟨p, ?_⟩
  intro i k
  obtain ⟨j, rfl⟩ := (Fintype.equivFin ι).symm.surjective i
  exact hp j k

/-- If an open subsource has finite structural map after base change,
its actual open inclusion into the pulled-back separated source is also
finite, hence closed. -/
theorem isClopen_preimage_range_of_finite_pullback
    {U Y X T : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    (f : Y ⟶ X) [IsSeparated f] (t : T ⟶ X)
    [IsFinite (pullback.snd (j ≫ f) t)] :
    IsClopen ((pullback.fst f t) ⁻¹' Set.range j) := by
  let a : pullback j (pullback.fst f t) ⟶ pullback f t :=
    pullback.snd j (pullback.fst f t)
  have : IsFinite (a ≫ pullback.snd f t) := by
    change IsFinite (pullback.snd j (pullback.fst f t) ≫ pullback.snd f t)
    rw [← pullbackRightPullbackFstIso_hom_snd f t j]
    infer_instance
  have : IsFinite a := IsFinite.of_comp a (pullback.snd f t)
  have : IsClosedImmersion a :=
    (IsClosedImmersion.iff_isFinite_and_mono a).mpr ⟨inferInstance, inferInstance⟩
  rw [← Scheme.Pullback.range_snd]
  exact ⟨a.isClosedEmbedding.isClosed_range, a.isOpenEmbedding.isOpen_range⟩

/-- A principal affine open in an affine etale source becomes clopen in
the entire actual pulled-back source on an original finite partition. -/
theorem exists_clopen_partition_basicOpen {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : Y ⟶ X) [Etale f] (b : Γ(Y, ⊤)) :
    ∃ p : FiniteLocallyClosedPartition X,
      ∀ k, IsClopen ((pullback.fst f (p.inclusion k)) ⁻¹' (Y.basicOpen b : Set Y)) := by
  obtain ⟨p, hp⟩ := exists_finitePartition_of_isAffineHom_of_etale ((Y.basicOpen b).ι ≫ f)
  refine ⟨p, fun k => ?_⟩
  have := hp k
  simpa only [Scheme.Opens.range_ι] using
    isClopen_preimage_range_of_finite_pullback (Y.basicOpen b).ι f (p.inclusion k)

/-- An arbitrary constructible subset of an affine etale source becomes
clopen in the entire source over each actual part of a finite partition
of the affine base. -/
theorem exists_clopen_partition_of_isConstructible
    {X Y : Scheme.{u}} [IsAffine X] (f : Y ⟶ X) [IsAffineHom f] [Etale f]
    {s : Set Y} (hs : Topology.IsConstructible s) :
    ∃ p : FiniteLocallyClosedPartition X,
      ∀ k, IsClopen ((pullback.fst f (p.inclusion k)) ⁻¹' s) := by
  have : IsAffine Y := isAffine_of_isAffineHom f
  induction hs using Topology.IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen hUcomp =>
    obtain ⟨b, hb, hU⟩ :=
      isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen.mp ⟨hUcomp.isCompact, hUopen⟩
    let := hb.fintype
    obtain ⟨p, hp⟩ := exists_common_clopen_partition f
      (fun x : b => (Y.basicOpen x.val : Set Y))
      (fun x => exists_clopen_partition_basicOpen f x.val)
    refine ⟨p, fun k => ?_⟩
    rw [hU]
    simp only [Set.preimage_iUnion]
    exact hb.isClopen_biUnion fun x hx => hp ⟨x, hx⟩ k
  | union s hs t ht ihs iht =>
    obtain ⟨p, hp⟩ := ihs
    obtain ⟨q, hq⟩ := iht
    refine ⟨p.intersection q, fun k => ?_⟩
    rw [Set.preimage_union]
    exact ((p.intersectionRefinesLeft q).isClopen_preimage f s hp k).union
      ((p.intersectionRefinesRight q).isClopen_preimage f t hq k)
  | compl s hs ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p, fun k => ?_⟩
    simpa only [Set.preimage_compl] using (hp k).compl

/-- An affine etale map and any finite family of original constructible
subsets admit one actual finite locally closed base partition. On every
part the structural map is finite, and every original subset pulls back
to a clopen subset of the entire pulled-back source. No Noetherianity,
reducedness, surjectivity, or pre-existing common partition is assumed. -/
theorem exists_finite_clopen_partition_of_isAffineHom_of_etale
    {X Y : Scheme.{u}} [IsAffine X] (f : Y ⟶ X) [IsAffineHom f] [Etale f]
    {ι : Type v} [Finite ι] (s : ι → Set Y) (hs : ∀ i, Topology.IsConstructible (s i)) :
    ∃ p : FiniteLocallyClosedPartition X,
      (∀ k, IsFinite (pullback.snd f (p.inclusion k))) ∧
      ∀ i k, IsClopen ((pullback.fst f (p.inclusion k)) ⁻¹' s i) := by
  obtain ⟨p, hp⟩ := exists_finitePartition_of_isAffineHom_of_etale f
  obtain ⟨q, hq⟩ := exists_common_clopen_partition f s
    (fun i => exists_clopen_partition_of_isConstructible f (hs i))
  refine ⟨p.intersection q, (p.intersectionRefinesLeft q).isFinite_pullback_snd f hp, ?_⟩
  intro i
  exact (p.intersectionRefinesRight q).isClopen_preimage f (s i) (hq i)

/-- Specialization to the original supports of an actual upstairs
partition; each whole original stratum preimage is clopen. -/
theorem exists_finite_clopen_partition_of_partition
    {X Y : Scheme.{u}} [IsAffine X] (f : Y ⟶ X) [IsAffineHom f] [Etale f]
    (q : FiniteLocallyClosedPartition Y) :
    ∃ p : FiniteLocallyClosedPartition X,
      (∀ k, IsFinite (pullback.snd f (p.inclusion k))) ∧
      ∀ i k, IsClopen ((pullback.fst f (p.inclusion k)) ⁻¹' Set.range (q.inclusion i)) :=
  exists_finite_clopen_partition_of_isAffineHom_of_etale f
    (fun i => Set.range (q.inclusion i)) q.constructible_range

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
