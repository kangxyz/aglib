/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.ClosureLocallyConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.Partitions
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.Values

/-! # Weak-Serre closure of original finite abelian constructibility

On each affine open, the original endpoint partitions have a common actual
refinement. Every stratum is qcqs, so its finite abelian local systems admit
positive scalar bounds. The genuine finite-ring module closure then applies
to the original restricted kernel, cokernel or short exact sequence. The
base scheme is arbitrary; no arbitrary-subobject closure is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible

universe u

attribute [local instance] hasSheafifyLarge

private theorem common_partition_pair {X : Scheme.{u}}
    {F G : AbelianSheaf.{u, u + 1} X}
    (hF : Nonempty (ConstructiblePartition F)) (hG : Nonempty (ConstructiblePartition G)) :
    ∃ p : FiniteLocallyClosedPartition X,
      (∀ i, IsFiniteLocallyConstant ((inverseImage (p.inclusion i)).obj F)) ∧
      (∀ i, IsFiniteLocallyConstant ((inverseImage (p.inclusion i)).obj G)) := by
  obtain ⟨t⟩ := hF
  obtain ⟨s⟩ := hG
  let p := t.toFiniteLocallyClosedPartition
  let q := s.toFiniteLocallyClosedPartition
  exact ⟨p.intersection q,
    (p.intersectionRefinesLeft q).isFiniteLocallyConstant t.locally_constant,
    (p.intersectionRefinesRight q).isFiniteLocallyConstant s.locally_constant⟩

private theorem compact_partition_stratum {X : Scheme.{u}} [CompactSpace X]
    (p : FiniteLocallyClosedPartition X) (i : Fin p.count) :
    CompactSpace (p.stratum i) := by
  have : IsImmersion (p.inclusion i) := p.immersion i
  constructor
  apply (p.inclusion i).isEmbedding.isCompact_iff.mpr
  rw [Set.image_univ]
  exact isCompact_of_constructible _ (p.constructible_range i)

private theorem quasiSeparated_partition_stratum {X : Scheme.{u}}
    [QuasiSeparatedSpace X] (p : FiniteLocallyClosedPartition X) (i : Fin p.count) :
    QuasiSeparatedSpace (p.stratum i) := by
  have : IsImmersion (p.inclusion i) := p.immersion i
  exact quasiSeparatedSpace_of_quasiSeparated (p.inclusion i)

/-- Kernels between original constructible finite abelian coefficients
remain constructible on every scheme. -/
theorem isConstructible_kernel {X : Scheme.{u}}
    {F G : AbelianSheaf.{u, u + 1} X} (f : F ⟶ G)
    (hF : IsConstructible F) (hG : IsConstructible G) :
    IsConstructible (kernel f) := by
  intro U
  have : IsAffine U.1.toScheme := U.2
  obtain ⟨p, hpF, hpG⟩ := common_partition_pair (hF U) (hG U)
  refine ⟨{ toFiniteLocallyClosedPartition := p, locally_constant := ?_ }⟩
  intro i
  have := compact_partition_stratum p i
  have := quasiSeparated_partition_stratum p i
  let P := inverseImage U.1.ι ⋙ inverseImage (p.inclusion i)
  exact (isFiniteLocallyConstant_iff_of_iso (PreservesKernel.iso P f)).mpr
    (isFiniteLocallyConstant_kernel_of_qcqs (P.map f) (hpF i) (hpG i))

/-- Cokernels between original constructible finite abelian coefficients
remain constructible on every scheme. -/
theorem isConstructible_cokernel {X : Scheme.{u}}
    {F G : AbelianSheaf.{u, u + 1} X} (f : F ⟶ G)
    (hF : IsConstructible F) (hG : IsConstructible G) :
    IsConstructible (cokernel f) := by
  intro U
  have : IsAffine U.1.toScheme := U.2
  obtain ⟨p, hpF, hpG⟩ := common_partition_pair (hF U) (hG U)
  refine ⟨{ toFiniteLocallyClosedPartition := p, locally_constant := ?_ }⟩
  intro i
  have := compact_partition_stratum p i
  have := quasiSeparated_partition_stratum p i
  let P := inverseImage U.1.ι ⋙ inverseImage (p.inclusion i)
  exact (isFiniteLocallyConstant_iff_of_iso (PreservesCokernel.iso P f)).mpr
    (isFiniteLocallyConstant_cokernel_of_qcqs (P.map f) (hpF i) (hpG i))

/-- The original middle coefficient of a short exact sequence with
constructible finite abelian endpoints is constructible on every scheme. -/
theorem isConstructible_extension {X : Scheme.{u}}
    (S : ShortComplex (AbelianSheaf.{u, u + 1} X)) (hS : S.ShortExact)
    (h₁ : IsConstructible S.X₁) (h₃ : IsConstructible S.X₃) :
    IsConstructible S.X₂ := by
  intro U
  have : IsAffine U.1.toScheme := U.2
  obtain ⟨p, hp₁, hp₃⟩ := common_partition_pair (h₁ U) (h₃ U)
  refine ⟨{ toFiniteLocallyClosedPartition := p, locally_constant := ?_ }⟩
  intro i
  have := compact_partition_stratum p i
  have := quasiSeparated_partition_stratum p i
  let P := inverseImage U.1.ι ⋙ inverseImage (p.inclusion i)
  exact isFiniteLocallyConstant_extension_of_qcqs (S.map P) (hS.map_of_exact P)
    (hp₁ i) (hp₃ i)

/-- Native constructibility respects original coefficient isomorphisms. -/
instance isConstructible_isoClosed (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsConstructible (X := X)) where
  of_iso e h := (isConstructible_iff_of_iso e).mp h

/-- The original constructibility predicate contains the actual zero sheaf. -/
instance isConstructible_containsZero (X : Scheme.{u}) :
    ObjectProperty.ContainsZero (IsConstructible (X := X)) where
  exists_zero := ⟨0, isZero_zero _, isConstructible_of_isFiniteLocallyConstant
    (FiniteColimits.isFiniteLocallyConstant_of_isZero (isZero_zero _))⟩

/-- Native weak kernel closure of original finite abelian constructibility. -/
instance isConstructible_closedUnderKernels (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderKernels (IsConstructible (X := X)) where
  kernels_le := by
    rintro _ ⟨f, k, hk, hF, hG⟩
    exact (isConstructible_iff_of_iso
      (hk.conePointUniqueUpToIso (kernelIsKernel f))).mpr (isConstructible_kernel f hF hG)

/-- Native weak cokernel closure of original finite abelian constructibility. -/
instance isConstructible_closedUnderCokernels (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderCokernels (IsConstructible (X := X)) where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hF, hG⟩
    exact (isConstructible_iff_of_iso
      (hk.coconePointUniqueUpToIso (cokernelIsCokernel f))).mpr (isConstructible_cokernel f hF hG)

/-- Native extension closure retains the actual middle coefficient. -/
instance isConstructible_closedUnderExtensions (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderExtensions (IsConstructible (X := X)) where
  prop_X₂_of_shortExact hS hF hG := isConstructible_extension _ hS hF hG

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible
