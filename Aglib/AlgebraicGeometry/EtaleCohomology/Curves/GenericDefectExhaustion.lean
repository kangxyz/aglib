/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FiniteSupportExhaustion
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericCokernelSupport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericKernelSheafSupport

/-! # Actual finite closed support exhaustion of the generic-unit defects -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Set
open GroupCohomology.Kummer.Coefficients

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} [IsNoetherian X]

/-- A kernel section is genuinely locally zero at each generic point of the test. -/
theorem genericKernel_generic_mem_zeroLocus (U : X.Etale) [QuasiCompact U.hom]
    (a : (kernel (genericArtinUnit X)).obj.obj (op U)) (η : genericPoints U.left) :
    η.val ∈ Etale.sectionZeroLocus (kernel (genericArtinUnit X)).obj a := by
  let ι := kernel.ι (genericArtinUnit X)
  let b := ι.hom.app (op U) a
  have hb : (genericArtinUnit X).hom.app (op U) b = 0 := by
    have h := congrArg (fun k : kernel (genericArtinUnit X) ⟶
      (directImage (genericArtinMap X)).obj (gm (genericArtinLocus X)) =>
        k.hom.app (op U)) (kernel.condition (genericArtinUnit X))
    exact ConcreteCategory.congr_hom h a
  obtain ⟨V, f, y, hy, hz⟩ := Kummer.mem_gm_sectionZeroLocus_of_germ_eq_one U b η.val
    (genericUnit_kernel_generic_germs U b hb η)
  refine ⟨V, f, y, hy, ?_⟩
  apply (AddCommGrpCat.mono_iff_injective (ι.hom.app (op V))).mp inferInstance
  rw [map_zero]
  exact (ConcreteCategory.congr_hom (ι.hom.naturality f.op) a).trans hz

private theorem quasiCompact_affine_test (U : X.Etale) (hU : IsAffine U.left) :
    QuasiCompact U.hom := by
  let : IsAffine U.left := hU
  let : IsLocallyNoetherian U.left :=
    LocallyOfFiniteType.isLocallyNoetherian (X := U.left) (Y := X) U.hom
  let : IsNoetherian U.left := {
    toIsLocallyNoetherian := inferInstance
    toCompactSpace := inferInstance }
  exact quasiCompact_of_noetherianSpace_source (X := U.left) (Y := X) U.hom

/-- The original kernel is its actual filtered colimit of finite closed support subobjects. -/
theorem genericKernel_finiteSupportColimit_isIso (hdim : topologicalKrullDim X ≤ 1) :
    IsIso (finiteSupportColimitMap (kernel (genericArtinUnit X))) := by
  apply finiteSupportColimitMap_isIso _ hdim
  intro U hU a x hx
  let : QuasiCompact U.hom := quasiCompact_affine_test U hU
  exact genericKernel_generic_mem_zeroLocus U a ⟨x, hx⟩

/-- The original cokernel is its actual filtered colimit of finite closed support subobjects. -/
theorem genericCokernel_finiteSupportColimit_isIso (hdim : topologicalKrullDim X ≤ 1) :
    IsIso (finiteSupportColimitMap (cokernel (genericArtinUnit X))) := by
  apply finiteSupportColimitMap_isIso _ hdim
  intro U hU a x hx
  let : QuasiCompact U.hom := quasiCompact_affine_test U hU
  exact genericCokernel_generic_mem_zeroLocus U a ⟨x, hx⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
