/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.Partitions

/-! # Module restrictions on the original common constructible partitions

The geometric partition and refinement maps are the existing native ones.
Only the finite-type module restriction is transported here. No second
partition or constructibility model is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

/-- Actual geometric refinement preserves the original finite-type module
restrictions through the native inverse-image composition comparison. -/
theorem FiniteLocallyClosedPartition.Refinement.isFiniteTypeLocallyConstant
    {X : Scheme.{u}} {q p : FiniteLocallyClosedPartition X} (r : q.Refinement p)
    {F : Modules.ModuleSheaf R X}
    (hF : ∀ i, Modules.IsFiniteTypeLocallyConstant
      ((Modules.moduleInverseImage R (p.inclusion i)).obj F)) :
    ∀ j, Modules.IsFiniteTypeLocallyConstant
      ((Modules.moduleInverseImage R (q.inclusion j)).obj F) := by
  intro j
  rw [← r.comm j]
  exact (Modules.isFiniteTypeLocallyConstant_iff_of_iso
    ((Modules.moduleInverseImageComp R (p.inclusion (r.indexMap j)) (r.map j)).app F)).mpr
      (Modules.isFiniteTypeLocallyConstant_pullback (r.map j) (hF (r.indexMap j)))

namespace Modules

/-- Refinement keeps the original module coefficient and all actual stratum maps. -/
def ConstructiblePartition.refine {X : Scheme.{u}} {F : ModuleSheaf R X}
    (t : ConstructiblePartition F) (q : FiniteLocallyClosedPartition X)
    (r : q.Refinement t.toFiniteLocallyClosedPartition) : ConstructiblePartition F where
  toFiniteLocallyClosedPartition := q
  locally_constant := r.isFiniteTypeLocallyConstant t.locally_constant

/-- Two module coefficients with actual finite partitions have an original
common partition, given by the already constructed geometric intersection. -/
theorem exists_common_partition_pair {X : Scheme.{u}} {F G : ModuleSheaf R X}
    (hF : Nonempty (ConstructiblePartition F)) (hG : Nonempty (ConstructiblePartition G)) :
    ∃ p : FiniteLocallyClosedPartition X,
      (∀ i, IsFiniteTypeLocallyConstant ((moduleInverseImage R (p.inclusion i)).obj F)) ∧
      (∀ i, IsFiniteTypeLocallyConstant ((moduleInverseImage R (p.inclusion i)).obj G)) := by
  obtain ⟨t⟩ := hF
  obtain ⟨s⟩ := hG
  let p := t.toFiniteLocallyClosedPartition
  let q := s.toFiniteLocallyClosedPartition
  exact ⟨p.intersection q,
    (p.intersectionRefinesLeft q).isFiniteTypeLocallyConstant t.locally_constant,
    (p.intersectionRefinesRight q).isFiniteTypeLocallyConstant s.locally_constant⟩

end Modules

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
