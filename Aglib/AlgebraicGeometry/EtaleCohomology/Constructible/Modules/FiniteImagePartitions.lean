/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Pullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.Composition

/-! # Genuine module constructibility on actual Noetherian strata

Finite partitions of the original stratum restrictions are composed, not
replaced by a new coefficient predicate. Noetherianity is a hypothesis on the
base scheme, not the coefficient ring. The actual maps from each refining
stratum are retained through native inverse-image composition.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

/-- Compose actual finite module partitions along a given actual Noetherian
geometric partition. -/
theorem nonempty_constructiblePartition_of_noetherian_partition
    {X : Scheme.{u}} [IsNoetherian X]
    (p : FiniteLocallyClosedPartition X) (F : ModuleSheaf R X)
    (hF : ∀ i, IsConstructible ((moduleInverseImage R (p.inclusion i)).obj F)) :
    Nonempty (ConstructiblePartition F) := by
  classical
  have hcompact (i) : CompactSpace (p.stratum i) := by
    have := p.immersion i
    constructor
    apply (p.inclusion i).isEmbedding.isCompact_iff.mpr
    rw [Set.image_univ]
    exact TopologicalSpace.NoetherianSpace.isCompact _
  have hqs (i) : QuasiSeparatedSpace (p.stratum i) := by
    have := p.immersion i
    exact quasiSeparatedSpace_of_quasiSeparated (p.inclusion i)
  let q (i) : ConstructiblePartition ((moduleInverseImage R (p.inclusion i)).obj F) := by
    have := hcompact i
    have := hqs i
    exact Classical.choice (nonempty_constructiblePartition (hF i))
  let t := FiniteLocallyClosedPartition.compose p
    (fun i => (q i).toFiniteLocallyClosedPartition)
  refine ⟨{ toFiniteLocallyClosedPartition := t, locally_constant := ?_ }⟩
  intro a
  let ij := (Fintype.equivFin (Σ i, Fin (q i).count)).symm a
  change IsFiniteTypeLocallyConstant ((moduleInverseImage R
    ((q ij.1).inclusion ij.2 ≫ p.inclusion ij.1)).obj F)
  exact (isFiniteTypeLocallyConstant_iff_of_iso
    ((moduleInverseImageComp R (p.inclusion ij.1) ((q ij.1).inclusion ij.2)).app F)).mpr
      ((q ij.1).locally_constant ij.2)

/-- Actual finite locally closed strata detect genuine constructibility over
Noetherian schemes, without Noetherianity of the coefficient ring. -/
theorem isConstructible_of_noetherian_partition {X : Scheme.{u}} [IsNoetherian X]
    (p : FiniteLocallyClosedPartition X) {F : ModuleSheaf R X}
    (hF : ∀ i, IsConstructible ((moduleInverseImage R (p.inclusion i)).obj F)) :
    IsConstructible F := by
  obtain ⟨t⟩ := nonempty_constructiblePartition_of_noetherian_partition p F hF
  intro U
  have : IsAffine U.1.toScheme := U.property
  exact ⟨t.baseChange U.1.ι⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
