/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # The original sections of a kernel are the kernel of the original section map -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {X : Scheme.{u}} {M N : X.Modules} (p : M ⟶ N) (U : X.Opens)

local instance : (SheafOfModules.evaluation X.ringCatSheaf (op U)).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Evaluation preserves the actual kernel, and the native module-category
kernel is the original linear-map kernel. No affine hypothesis is needed. -/
def kernelSectionsIso :
    ModuleCat.of Γ(X, U) Γ(kernel p, U) ≅ ModuleCat.of Γ(X, U) (p.val.app (op U)).hom.ker :=
  PreservesKernel.iso (SheafOfModules.evaluation X.ringCatSheaf (op U)) p ≪≫
    ModuleCat.kernelIsoKer ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map p)

@[reassoc (attr := simp)]
theorem kernelSectionsIso_hom_subtype :
    (kernelSectionsIso p U).hom ≫ ModuleCat.ofHom (p.val.app (op U)).hom.ker.subtype =
      (kernel.ι p).val.app (op U) := by
  let : (SheafOfModules.evaluation X.ringCatSheaf (op U)).PreservesZeroMorphisms :=
    ⟨fun _ _ => rfl⟩
  simp only [kernelSectionsIso, Iso.trans_hom, Category.assoc,
    PreservesKernel.iso_hom]
  exact kernelComparison_comp_ι p (SheafOfModules.evaluation X.ringCatSheaf (op U))

/-- Linear coordinates retain the original kernel inclusion exactly. -/
def kernelSectionsLinearEquiv : Γ(kernel p, U) ≃ₗ[Γ(X, U)] (p.val.app (op U)).hom.ker :=
  (kernelSectionsIso p U).toLinearEquiv

@[simp]
theorem kernelSectionsLinearEquiv_apply (x : Γ(kernel p, U)) :
    (kernelSectionsLinearEquiv p U x).val = (kernel.ι p).app U x :=
  congrArg (fun k => k x) (kernelSectionsIso_hom_subtype p U)

end AlgebraicGeometry.Scheme.Modules
