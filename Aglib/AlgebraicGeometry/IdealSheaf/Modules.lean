/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Actual kernel ideal modules of scheme morphisms

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors.lean`, SHA-256
  `605837ddfb7404b51e4350a71863645478453f00ac338cfe26c4d43efe8490c7`.
- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/BaseChange.lean`, SHA-256
  `a5df3d28102fc6b3724618d2b1c94f913572db922d9f3ce48f6f9b1e2aa06faa`.
- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/Graph.lean`, SHA-256
  `47ec21fd6636d8c6a5187cc30ed3cdcfcccc948558e4d2bd75d54a2466725a8d`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `doc/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open LinearMap

section
namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The actual structure-module map from the target unit module to the pushed source unit module. -/
def structureModuleMap (f : X ⟶ Y) :
    (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

@[simp] theorem structureModuleMap_app (f : X ⟶ Y) (U : Y.Opens) (a : Γ(Y,U)) :
    (structureModuleMap f).val.app (op U) a = f.app U a := rfl

/-- The actual module kernel of the structure-module map of an arbitrary scheme morphism. -/
def idealModule (f : X ⟶ Y) : Y.Modules := kernel (structureModuleMap f)

/-- The canonical inclusion of the actual kernel ideal module into the structure module. -/
def idealInclusion (f : X ⟶ Y) :
    idealModule f ⟶ (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf) :=
  kernel.ι (structureModuleMap f)

/-- The actual kernel ideal inclusion is a monomorphism. -/
instance idealInclusionMono (f : X ⟶ Y) : Mono (idealInclusion f) := by
  dsimp [idealInclusion]; infer_instance

@[reassoc (attr := simp)] theorem idealInclusion_structureMap (f : X ⟶ Y) :
    idealInclusion f ≫ structureModuleMap f = 0 := kernel.condition _

/-- Sections of the actual kernel module identify with the kernel of the actual section map. -/
def idealSectionsIso (f : X ⟶ Y) (U : Y.Opens) :
    (idealModule f).val.obj (op U) ≅
      ModuleCat.of Γ(Y,U) ((structureModuleMap f).val.app (op U)).hom.ker := by
  let ev : Y.Modules ⥤ ModuleCat Γ(Y,U) :=
    SheafOfModules.evaluation Y.ringCatSheaf (op U)
  haveI : PreservesLimits ev := inferInstanceAs
    (PreservesLimits (SheafOfModules.evaluation Y.ringCatSheaf (op U)))
  exact (PreservesKernel.iso ev (structureModuleMap f)) ≪≫ ModuleCat.kernelIsoKer _

/-- The linear identification of actual ideal sections with the ring-section kernel. -/
def idealSectionsEquiv (f : X ⟶ Y) (U : Y.Opens) :
    (idealModule f).val.obj (op U) ≃ₗ[Γ(Y,U)] RingHom.ker (f.app U).hom :=
  CategoryTheory.Iso.toLinearEquiv (idealSectionsIso f U)

theorem idealSectionsEquiv_val (f : X ⟶ Y) (U : Y.Opens)
    (a : (idealModule f).val.obj (op U)) :
    (idealSectionsEquiv f U a : Γ(Y,U)) = (idealInclusion f).val.app (op U) a := by
  let ev : Y.Modules ⥤ ModuleCat Γ(Y,U) :=
    SheafOfModules.evaluation Y.ringCatSheaf (op U)
  have : PreservesLimits ev := inferInstanceAs
    (PreservesLimits (SheafOfModules.evaluation Y.ringCatSheaf (op U)))
  have h : (PreservesKernel.iso ev (structureModuleMap f)).hom ≫
      kernel.ι (ev.map (structureModuleMap f)) = ev.map (kernel.ι (structureModuleMap f)) := by
    rw [← PreservesKernel.iso_inv_ι ev (structureModuleMap f), ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  have h' := ModuleCat.kernelIsoKer_hom_ker_subtype (ev.map (structureModuleMap f))
  exact congrArg (fun k ↦ k.hom a) ((Category.assoc _ _ _).trans
    ((congrArg (fun k ↦ (PreservesKernel.iso ev (structureModuleMap f)).hom ≫ k) h').trans h))

end AlgebraicGeometry.Scheme.Hom
end

section
namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Z : Scheme.{u}}

@[reassoc]
theorem structureModuleMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    structureModuleMap (f ≫ g) = structureModuleMap g ≫
      (Scheme.Modules.pushforward g).map (structureModuleMap f) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app (SheafOfModules.unit X.ringCatSheaf) := by
  ext U a
  rfl

@[reassoc (attr := simp)]
theorem structureModuleMap_congr {f g : X ⟶ Y} (h : f = g) :
    structureModuleMap f ≫
      (Scheme.Modules.pushforwardCongr h).hom.app (SheafOfModules.unit X.ringCatSheaf) =
      structureModuleMap g := by
  subst h
  apply Scheme.Modules.hom_ext
  intro U
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardCongr_hom_app_app]
  simp

/-- The structure-module map of a scheme isomorphism is an isomorphism. -/
instance structureModuleMap_isIso (f : X ⟶ Y) [IsIso f] : IsIso (structureModuleMap f) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  change IsIso (((forget₂ CommRingCat RingCat) ⋙ forget₂ RingCat AddCommGrpCat).map (f.app U))
  infer_instance

end AlgebraicGeometry.Scheme.Hom
end
