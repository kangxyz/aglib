/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Kernel and cokernel closure under exact inverse image

The original functor and its native preservation isomorphisms transport the
weak closure properties. No ambient subobject or quotient closure is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- Pull back kernel closure along the original kernel-preserving functor. -/
instance inverseImage_closedUnderKernels [P.IsClosedUnderKernels]
    [PreservesFiniteLimits F] : (P.inverseImage F).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact P.prop_of_iso
      ((F.mapIso (hk.conePointUniqueUpToIso (kernelIsKernel f))) ≪≫
        PreservesKernel.iso F f).symm
      (P.prop_kernel (F.map f) hX hY)

/-- Pull back cokernel closure along the original cokernel-preserving functor. -/
instance inverseImage_closedUnderCokernels [P.IsClosedUnderCokernels]
    [PreservesFiniteColimits F] : (P.inverseImage F).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hX, hY⟩
    exact P.prop_of_iso
      ((F.mapIso (hk.coconePointUniqueUpToIso (cokernelIsCokernel f))) ≪≫
        PreservesCokernel.iso F f).symm
      (P.prop_cokernel (F.map f) hX hY)

end CategoryTheory.ObjectProperty
