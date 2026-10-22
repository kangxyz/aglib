/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineAnnihilation
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedDefects
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Morphisms

/-!
# Original affine sections of bounded sheaf defects

Ordinary affine kernels and cokernels are identified through the actual
tilde/global-section counit. Thus geometric annihilation bounds the kernel
and cokernel of the original affine section map with the same exponent.
There is no assumption that ordinary formal kernels are cartesian systems.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable {B : CommRingCat.{u}} {M N : (Spec B).Modules}
  [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)

/-- The affine cokernel is the tilde of the original section-map cokernel,
using the original counit square. -/
def affineDefectCokernelIso :
    tilde (cokernel (moduleSpecΓFunctor.map f)) ≅ cokernel f :=
  PreservesCokernel.iso (tilde.functor B) (moduleSpecΓFunctor.map f) ≪≫
    cokernel.mapIso _ f (asIso M.fromTildeΓ) (asIso N.fromTildeΓ)
      ((tilde.adjunction (R := B)).counit.naturality f)

/-- The actual section-map kernel is the original section module of the
ordinary sheaf kernel. -/
def affineDefectKernelSectionsEquiv :
    (moduleSpecΓFunctor.map f).hom.ker ≃ₗ[B] moduleSpecΓFunctor.obj (kernel f) :=
  ((ModuleCat.kernelIsoKer (moduleSpecΓFunctor.map f)).symm ≪≫
    tilde.toTildeΓNatIso.app (kernel (moduleSpecΓFunctor.map f)) ≪≫
    moduleSpecΓFunctor.mapIso (affineQuasicoherentKernelIso f)).toLinearEquiv

/-- The actual section-map cokernel is the original section module of the
ordinary sheaf cokernel. -/
def affineDefectCokernelSectionsEquiv :
    (moduleSpecΓFunctor.obj N ⧸ (moduleSpecΓFunctor.map f).hom.range) ≃ₗ[B]
      moduleSpecΓFunctor.obj (cokernel f) :=
  ((ModuleCat.cokernelIsoRangeQuotient (moduleSpecΓFunctor.map f)).symm ≪≫
    tilde.toTildeΓNatIso.app (cokernel (moduleSpecΓFunctor.map f)) ≪≫
    moduleSpecΓFunctor.mapIso (affineDefectCokernelIso f)).toLinearEquiv

/-- An original geometric kernel bound is the same ideal-power bound on
the kernel of the original affine section map. -/
theorem affineSections_kernel_bound (K : (Spec B).IdealSheafData) (t : ℕ)
    (h : killedByIdealSheaf (K ^ t) (kernel f)) :
    affineIdeal B K ^ t • (moduleSpecΓFunctor.map f).hom.ker = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.smul_le.mpr
  intro a ha x hx
  have hann := affineIdeal_pow_le_annihilator_of_killed B K (kernel f) t h
  have hz : a • (⟨x, hx⟩ : (moduleSpecΓFunctor.map f).hom.ker) = 0 := by
    apply (affineDefectKernelSectionsEquiv f).injective
    rw [(affineDefectKernelSectionsEquiv f).map_smul, map_zero]
    exact (Module.mem_annihilator.mp (hann ha)) _
  exact congrArg Subtype.val hz

/-- An original geometric cokernel bound is the same ideal-power bound
on the cokernel of the original affine section map. -/
theorem affineSections_cokernel_bound (K : (Spec B).IdealSheafData) (t : ℕ)
    (h : killedByIdealSheaf (K ^ t) (cokernel f)) :
    affineIdeal B K ^ t • (⊤ : Submodule B (moduleSpecΓFunctor.obj N)) ≤
      (moduleSpecΓFunctor.map f).hom.range := by
  apply Submodule.smul_le.mpr
  intro a ha x hx
  apply (Submodule.Quotient.mk_eq_zero _).mp
  have hann := affineIdeal_pow_le_annihilator_of_killed B K (cokernel f) t h
  apply (affineDefectCokernelSectionsEquiv f).injective
  rw [Submodule.Quotient.mk_smul, (affineDefectCokernelSectionsEquiv f).map_smul, map_zero]
  exact (Module.mem_annihilator.mp (hann ha)) _

/-- A native affine section-kernel bound gives the actual geometric kernel
bound. This is used on the finite local reconstruction model. -/
theorem killed_kernel_of_affineSections_bound (K : (Spec B).IdealSheafData) (t : ℕ)
    (h : affineIdeal B K ^ t • (moduleSpecΓFunctor.map f).hom.ker = ⊥) :
    killedByIdealSheaf (K ^ t) (kernel f) := by
  apply (killed_iff_affineIdeal_le_annihilator B (K ^ t) (kernel f)).mpr
  rw [affineIdeal_pow]
  intro a ha
  rw [Module.mem_annihilator]
  intro m
  obtain ⟨x, rfl⟩ := (affineDefectKernelSectionsEquiv f).surjective m
  rw [← (affineDefectKernelSectionsEquiv f).map_smul]
  have hz := Submodule.smul_mem_smul ha x.property
  rw [h] at hz
  have hx : a • x = 0 := Subtype.ext hz
  rw [hx, map_zero]

/-- A native affine section-cokernel bound gives the actual geometric
cokernel bound, with the original ideal and exponent. -/
theorem killed_cokernel_of_affineSections_bound (K : (Spec B).IdealSheafData) (t : ℕ)
    (h : affineIdeal B K ^ t • (⊤ : Submodule B (moduleSpecΓFunctor.obj N)) ≤
      (moduleSpecΓFunctor.map f).hom.range) :
    killedByIdealSheaf (K ^ t) (cokernel f) := by
  let : (cokernel f).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec B).ringCatSheaf).prop_of_iso
      (affineDefectCokernelIso f) inferInstance
  apply (killed_iff_affineIdeal_le_annihilator B (K ^ t) (cokernel f)).mpr
  rw [affineIdeal_pow]
  intro a ha
  rw [Module.mem_annihilator]
  intro m
  obtain ⟨q, rfl⟩ := (affineDefectCokernelSectionsEquiv f).surjective m
  induction q using Submodule.Quotient.induction_on with
  | _ y =>
    rw [← (affineDefectCokernelSectionsEquiv f).map_smul]
    have hz : a • (Submodule.Quotient.mk y :
        moduleSpecΓFunctor.obj N ⧸ (moduleSpecΓFunctor.map f).hom.range) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr
        (h (Submodule.smul_mem_smul ha Submodule.mem_top))
    rw [hz, map_zero]

/-- A geometric formal defect bound controls the kernel and cokernel of
every original affine stage map. The formal and bounding ideals may differ. -/
theorem defectsKilled_affineSections_bounds [IsNoetherianRing B]
    {K : (Spec B).IdealSheafData} {F G : AdicSystem (Spec B) K}
    (φ : F ⟶ G) (J : (Spec B).IdealSheafData) (t : ℕ)
    (h : AdicSystem.DefectsKilled J t φ) (n : ℕ) :
    affineIdeal B J ^ t • (moduleSpecΓFunctor.map (φ.hom.app (op n))).hom.ker = ⊥ ∧
      affineIdeal B J ^ t •
        (⊤ : Submodule B (moduleSpecΓFunctor.obj (G.obj.obj (op n)))) ≤
          (moduleSpecΓFunctor.map (φ.hom.app (op n))).hom.range := by
  let : (F.obj.obj (op n)).IsQuasicoherent :=
    ((QuasiCoherent.affineLocallyFiniteType_spec_iff B _).mp (F.property.coherent n)).1
  let : (G.obj.obj (op n)).IsQuasicoherent :=
    ((QuasiCoherent.affineLocallyFiniteType_spec_iff B _).mp (G.property.coherent n)).1
  exact ⟨affineSections_kernel_bound (φ.hom.app (op n)) J t (h n).1,
    affineSections_cokernel_bound (φ.hom.app (op n)) J t (h n).2⟩

end AlgebraicGeometry.Scheme.Modules.Coherent
