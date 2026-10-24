/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructibleSums
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureProperties

/-! # Weak-Serre closure of constructible modules over a Noetherian ring

Kernels, cokernels and extensions are checked on the original affine opens
and the existing native common finite partitions. Exact original module
inverse image reduces each assertion to the proved local-system closure.
No arbitrary-subobject or arbitrary-quotient closure is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R] [IsNoetherianRing R]

local instance {X S : Scheme.{u}} (f : S ⟶ X) :
    (moduleInverseImage R f).IsLeftAdjoint :=
  (moduleImageAdjunction R f).isLeftAdjoint

/-- Kernels of arrows between constructible module coefficients are constructible. -/
theorem isConstructible_kernel {X : Scheme.{u}} {F G : ModuleSheaf R X}
    (φ : F ⟶ G) (hF : IsConstructible F) (hG : IsConstructible G) :
    IsConstructible (kernel φ) := by
  intro U
  obtain ⟨p, hpF, hpG⟩ := exists_common_partition_pair (hF U) (hG U)
  refine ⟨{ toFiniteLocallyClosedPartition := p, locally_constant := ?_ }⟩
  intro i
  let P := moduleInverseImage R U.1.ι ⋙ moduleInverseImage R (p.inclusion i)
  exact (isFiniteTypeLocallyConstant_iff_of_iso (PreservesKernel.iso P φ)).mpr
    (isFiniteTypeLocallyConstant_kernel (P.map φ) (hpF i) (hpG i))

/-- Cokernels of arrows between constructible module coefficients are constructible. -/
theorem isConstructible_cokernel {X : Scheme.{u}} {F G : ModuleSheaf R X}
    (φ : F ⟶ G) (hF : IsConstructible F) (hG : IsConstructible G) :
    IsConstructible (cokernel φ) := by
  intro U
  obtain ⟨p, hpF, hpG⟩ := exists_common_partition_pair (hF U) (hG U)
  refine ⟨{ toFiniteLocallyClosedPartition := p, locally_constant := ?_ }⟩
  intro i
  let P := moduleInverseImage R U.1.ι ⋙ moduleInverseImage R (p.inclusion i)
  exact (isFiniteTypeLocallyConstant_iff_of_iso (PreservesCokernel.iso P φ)).mpr
    (isFiniteTypeLocallyConstant_cokernel (P.map φ) (hpF i) (hpG i))

/-- The original middle term of a short exact sequence of constructible
module coefficients is constructible. -/
theorem isConstructible_extension {X : Scheme.{u}}
    (S : ShortComplex (ModuleSheaf R X)) (hS : S.ShortExact)
    (h₁ : IsConstructible S.X₁) (h₃ : IsConstructible S.X₃) :
    IsConstructible S.X₂ := by
  intro U
  obtain ⟨p, hp₁, hp₃⟩ := exists_common_partition_pair (h₁ U) (h₃ U)
  refine ⟨{ toFiniteLocallyClosedPartition := p, locally_constant := ?_ }⟩
  intro i
  let P := moduleInverseImage R U.1.ι ⋙ moduleInverseImage R (p.inclusion i)
  exact isFiniteTypeLocallyConstant_extension (S.map P) (hS.map_of_exact P) (hp₁ i) (hp₃ i)

/-- Native weak kernel closure, without arbitrary ambient subobjects. -/
instance isConstructible_closedUnderKernels (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderKernels (IsConstructible (R := R) (X := X)) where
  kernels_le := by
    rintro _ ⟨f, k, hk, hF, hG⟩
    exact (isConstructible_iff_of_iso
      (hk.conePointUniqueUpToIso (kernelIsKernel f))).mpr (isConstructible_kernel f hF hG)

/-- Native weak cokernel closure, without arbitrary ambient quotients. -/
instance isConstructible_closedUnderCokernels (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderCokernels (IsConstructible (R := R) (X := X)) where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hF, hG⟩
    exact (isConstructible_iff_of_iso
      (hk.coconePointUniqueUpToIso (cokernelIsCokernel f))).mpr (isConstructible_cokernel f hF hG)

/-- Native extension closure of the existing constructibility predicate. -/
instance isConstructible_closedUnderExtensions (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderExtensions (IsConstructible (R := R) (X := X)) where
  prop_X₂_of_shortExact hS hF hG := isConstructible_extension _ hS hF hG

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
