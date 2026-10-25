/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Data.Fintype.EquivFin

/-! # Actual common constructible partitions

The common refinement of two partitions consists of their actual scheme
fibre products. Its ranges are the intersections of the original ranges.
The original inverse-image coefficients remain finite locally constant
after this refinement. Induction gives a common partition for every finite
family, including the empty family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u v

attribute [local instance] hasSheafifyLarge

namespace FiniteLocallyClosedPartition

variable {X : Scheme.{u}}

/-- Package a finite indexed family of actual immersions as a partition.
The reindexing changes only the finite labels. -/
def ofFintype {ι : Type v} [Fintype ι] (S : ι → Scheme.{u})
    (f : ∀ i, S i ⟶ X) (hf : ∀ i, IsImmersion (f i))
    (hc : ∀ i, Topology.IsConstructible (Set.range (f i)))
    (hd : Pairwise fun i j => Disjoint (Set.range (f i)) (Set.range (f j)))
    (hcover : ∀ x : X, ∃ i, ∃ y : S i, f i y = x) :
    FiniteLocallyClosedPartition X where
  count := Fintype.card ι
  stratum i := S ((Fintype.equivFin ι).symm i)
  inclusion i := f ((Fintype.equivFin ι).symm i)
  immersion i := hf _
  constructible_range i := hc _
  disjoint := by
    intro i j hij
    apply hd
    exact fun h => hij ((Fintype.equivFin ι).symm.injective h)
  covers x := by
    obtain ⟨i, y, hy⟩ := hcover x
    obtain ⟨j, rfl⟩ := (Fintype.equivFin ι).symm.surjective i
    exact ⟨j, y, hy⟩

/-- An actual refinement records its original maps over the base. -/
structure Refinement (q p : FiniteLocallyClosedPartition X) where
  indexMap : Fin q.count → Fin p.count
  map : ∀ i, q.stratum i ⟶ p.stratum (indexMap i)
  comm : ∀ i, map i ≫ p.inclusion (indexMap i) = q.inclusion i

/-- The actual intersection strata give a common finite locally closed
constructible partition, without a Noetherian hypothesis. -/
def intersection (p q : FiniteLocallyClosedPartition X) :
    FiniteLocallyClosedPartition X :=
  ofFintype (fun ij : Fin p.count × Fin q.count =>
    pullback (p.inclusion ij.1) (q.inclusion ij.2))
    (fun ij => pullback.fst (p.inclusion ij.1) (q.inclusion ij.2) ≫ p.inclusion ij.1)
    (by
      intro ij
      have := p.immersion ij.1
      have := q.immersion ij.2
      infer_instance)
    (by
      intro ij
      rw [Scheme.Pullback.range_fst_comp]
      exact (p.constructible_range ij.1).inter (q.constructible_range ij.2))
    (by
      intro ij kl hne
      rw [Scheme.Pullback.range_fst_comp, Scheme.Pullback.range_fst_comp]
      by_cases h : ij.1 = kl.1
      · have h' : ij.2 ≠ kl.2 := fun h' => hne (Prod.ext h h')
        exact (q.disjoint h').mono Set.inter_subset_right Set.inter_subset_right
      · exact (p.disjoint h).mono Set.inter_subset_left Set.inter_subset_left)
    (by
      intro x
      obtain ⟨i, y, hy⟩ := p.covers x
      obtain ⟨j, z, hz⟩ := q.covers x
      obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback y z (hy.trans hz.symm)
      exact ⟨(i, j), w, by simpa only [Scheme.Hom.comp_apply, hw] using hy⟩)

/-- Projection from an intersection stratum to the first original stratum. -/
def intersection_refines_left (p q : FiniteLocallyClosedPartition X) :
    Refinement (p.intersection q) p where
  indexMap i := ((Fintype.equivFin (Fin p.count × Fin q.count)).symm i).1
  map _ := pullback.fst _ _
  comm _ := rfl

/-- Projection from an intersection stratum to the second original stratum. -/
def intersection_refines_right (p q : FiniteLocallyClosedPartition X) :
    Refinement (p.intersection q) q where
  indexMap i := ((Fintype.equivFin (Fin p.count × Fin q.count)).symm i).2
  map _ := pullback.snd _ _
  comm _ := pullback.condition.symm

/-- Finite local constancy of the original restrictions survives an actual
refinement, through the original inverse-image composition isomorphism. -/
theorem Refinement.isFiniteLocallyConstant {q p : FiniteLocallyClosedPartition X}
    (r : Refinement q p) {F : AbelianSheaf.{u, u + 1} X}
    (hF : ∀ i, IsFiniteLocallyConstant ((inverseImage (p.inclusion i)).obj F)) :
    ∀ j, IsFiniteLocallyConstant ((inverseImage (q.inclusion j)).obj F) := by
  intro j
  rw [← r.comm j]
  exact (isFiniteLocallyConstant_iff_of_iso
    ((inverseImageComp (p.inclusion (r.indexMap j)) (r.map j)).app F)).mpr
      (isFiniteLocallyConstant_pullback (r.map j) (hF (r.indexMap j)))

end FiniteLocallyClosedPartition

/-- Refining the actual partition retains a constructible coefficient's
original inverse-image restrictions. -/
def ConstructiblePartition.refine {X : Scheme.{u}} {F : AbelianSheaf.{u, u + 1} X}
    (t : ConstructiblePartition F) (q : FiniteLocallyClosedPartition X)
    (r : q.Refinement t.toFiniteLocallyClosedPartition) : ConstructiblePartition F where
  toFiniteLocallyClosedPartition := q
  locally_constant := r.isFiniteLocallyConstant t.locally_constant

/-- A finite sequence of actual constructible partitions has a common
partition with finite locally constant original restrictions. -/
theorem exists_common_partition_fin {X : Scheme.{u}} (r : ℕ)
    (F : Fin r → AbelianSheaf.{u, u + 1} X)
    (hF : ∀ i, Nonempty (ConstructiblePartition (F i))) :
    ∃ p : FiniteLocallyClosedPartition X,
      ∀ i j, IsFiniteLocallyConstant ((inverseImage (p.inclusion j)).obj (F i)) := by
  induction r with
  | zero => exact ⟨.singleton X, fun i => Fin.elim0 i⟩
  | succ r ih =>
    obtain ⟨p, hp⟩ := ih (fun i => F i.succ) (fun i => hF i.succ)
    obtain ⟨q⟩ := hF 0
    refine ⟨p.intersection q.toFiniteLocallyClosedPartition, ?_⟩
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact (p.intersection_refines_right q.toFiniteLocallyClosedPartition).isFiniteLocallyConstant
        q.locally_constant
    · exact (p.intersection_refines_left q.toFiniteLocallyClosedPartition).isFiniteLocallyConstant
        (hp k)

/-- Every finite family admits an actual common partition; the label
universe places no additional restriction on the coefficients. -/
theorem exists_common_partition {X : Scheme.{u}} {ι : Type v} [Finite ι]
    (F : ι → AbelianSheaf.{u, u + 1} X)
    (hF : ∀ i, Nonempty (ConstructiblePartition (F i))) :
    ∃ p : FiniteLocallyClosedPartition X,
      ∀ i j, IsFiniteLocallyConstant ((inverseImage (p.inclusion j)).obj (F i)) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨p, hp⟩ := exists_common_partition_fin (Fintype.card ι)
    (fun i => F ((Fintype.equivFin ι).symm i))
    (fun i => hF ((Fintype.equivFin ι).symm i))
  refine ⟨p, ?_⟩
  intro i j
  obtain ⟨k, rfl⟩ := (Fintype.equivFin ι).symm.surjective i
  exact hp k j

/-- On each original affine open, a finite family of geometrically
constructible coefficients admits a common actual partition. -/
theorem exists_common_partition_on_affine {X : Scheme.{u}} {ι : Type v} [Finite ι]
    (F : ι → AbelianSheaf.{u, u + 1} X) (hF : ∀ i, IsConstructible (F i))
    (U : X.affineOpens) :
    ∃ p : FiniteLocallyClosedPartition U.1.toScheme,
      ∀ i j, IsFiniteLocallyConstant
        ((inverseImage (p.inclusion j)).obj ((inverseImage U.1.ι).obj (F i))) :=
  exists_common_partition (fun i => (inverseImage U.1.ι).obj (F i)) (fun i => hF i U)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
