/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.LocallyConstant
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.RingTheory.Noetherian.Basic

/-! # Kernels and cokernels of actual constant module maps

The native constant sheaf functor takes the actual algebraic kernel and
cokernel to the original sheaf kernel and cokernel. Kernel finiteness uses
Noetherianity; cokernel finiteness needs only finite generation of the target.
These are chartwise suppliers, not closure claims for arbitrary sheaf maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R]

local instance closureConstantHasFiniteLimits : HasFiniteLimits (ModuleCat.{u + 1} R) where
  out _ _ _ := ModuleCat.hasLimitsOfShape.{0, 0, u + 1, r}

/-- The kernel of a genuine constant module map is constant of finite type
when its source is finite over a Noetherian coefficient ring. -/
theorem isFiniteTypeLocallyConstant_kernel_constantMap [IsNoetherianRing R]
    (X : Scheme.{u}) {M N : ModuleCat.{u + 1} R} [Module.Finite R M] (f : M ⟶ N) :
    IsFiniteTypeLocallyConstant
      (kernel ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).map f)) := by
  let C := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)
  let : PreservesFiniteLimits C :=
    Limits.comp_preservesFiniteLimits (Functor.const X.Etaleᵒᵖ)
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
  let : Module.Finite R ↥(kernel f : ModuleCat.{u + 1} R) :=
    Module.Finite.of_injective (kernel.ι f).hom
      ((ModuleCat.mono_iff_injective (kernel.ι f)).mp inferInstance)
  exact (isFiniteTypeLocallyConstant_iff_of_iso (PreservesKernel.iso C f)).mp
    (isFiniteTypeLocallyConstant_constant X (kernel f))

/-- The cokernel of a genuine constant module map is constant of finite type
as soon as its target is finite; no Noetherian assumption is required. -/
theorem isFiniteTypeLocallyConstant_cokernel_constantMap
    (X : Scheme.{u}) {M N : ModuleCat.{u + 1} R} [Module.Finite R N] (f : M ⟶ N) :
    IsFiniteTypeLocallyConstant
      (cokernel ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).map f)) := by
  let C := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)
  let : C.IsLeftAdjoint :=
    (constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} R)
      (etaleTerminalIsTerminal X)).isLeftAdjoint
  let : Module.Finite R ↥(cokernel f : ModuleCat.{u + 1} R) :=
    Module.Finite.of_surjective (cokernel.π f).hom
      ((ModuleCat.epi_iff_surjective (cokernel.π f)).mp inferInstance)
  exact (isFiniteTypeLocallyConstant_iff_of_iso (PreservesCokernel.iso C f)).mp
    (isFiniteTypeLocallyConstant_constant X (cokernel f))

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
