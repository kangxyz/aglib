/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureExtensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions

/-! # Native weak-Serre closure interfaces for finite-type local systems

The original module-sheaf predicate is closed under kernels, cokernels and
extensions. These native object-property interfaces do not claim closure under
arbitrary subobjects or quotients of an ambient sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R] [IsNoetherianRing R]

/-- Kernel closure concerns arrows whose source and target are local systems. -/
instance isFiniteTypeLocallyConstant_closedUnderKernels (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderKernels
      (IsFiniteTypeLocallyConstant (R := R) (X := X)) where
  kernels_le := by
    rintro _ ⟨f, k, hk, hF, hG⟩
    exact (isFiniteTypeLocallyConstant_iff_of_iso
      (hk.conePointUniqueUpToIso (kernelIsKernel f))).mpr
        (isFiniteTypeLocallyConstant_kernel f hF hG)

/-- Cokernel closure concerns arrows whose source and target are local systems. -/
instance isFiniteTypeLocallyConstant_closedUnderCokernels (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderCokernels
      (IsFiniteTypeLocallyConstant (R := R) (X := X)) where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hF, hG⟩
    exact (isFiniteTypeLocallyConstant_iff_of_iso
      (hk.coconePointUniqueUpToIso (cokernelIsCokernel f))).mpr
        (isFiniteTypeLocallyConstant_cokernel f hF hG)

/-- The actual middle term of a short exact sequence retains local constancy. -/
instance isFiniteTypeLocallyConstant_closedUnderExtensions (X : Scheme.{u}) :
    ObjectProperty.IsClosedUnderExtensions
      (IsFiniteTypeLocallyConstant (R := R) (X := X)) where
  prop_X₂_of_shortExact hS hF hG :=
    isFiniteTypeLocallyConstant_extension _ hS hF hG

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
