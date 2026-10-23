/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

/-! # The cokernel property of a quasi-isomorphic augmentation

No projectivity of the complex terms is required for this property.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex ChainComplex

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K : ChainComplex C ℕ} {Z : C} (π : K ⟶ (ChainComplex.single₀ C).obj Z)

lemma augmentation_d_comp : K.d 1 0 ≫ π.f 0 = 0 := by
  rw [← π.comm 1 0, single_obj_d, comp_zero]

/-- A quasi-isomorphic augmentation is the actual cokernel of the first
original differential; no projectivity hypothesis is needed. -/
def augmentationIsCokernel [QuasiIso π] :
    IsColimit (CokernelCofork.ofπ (π.f 0) (augmentation_d_comp π)) := by
  refine IsColimit.ofIsoColimit (K.opcyclesIsCokernel 1 0 (by simp)) ?_
  refine Cofork.ext (K.isoHomologyι₀.symm ≪≫ isoOfQuasiIsoAt π 0 ≪≫
    singleObjHomologySelfIso _ _ _) ?_
  rw [← cancel_mono (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 _).inv,
    ← cancel_mono (isoHomologyι₀ _).hom]
  dsimp
  simp only [isoHomologyι₀_inv_naturality_assoc, p_opcyclesMap_assoc, single₀_obj_zero,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, isoHomologyι_inv_hom_id,
    singleObjHomologySelfIso_inv_homologyι, singleObjOpcyclesSelfIso_hom,
    single₀ObjXSelf, Iso.refl_inv, Category.id_comp]

/-- The original first differential and augmentation form an exact sequence. -/
lemma augmentation_exact [QuasiIso π] :
    (ShortComplex.mk (K.d 1 0) (π.f 0) (augmentation_d_comp π)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (augmentationIsCokernel π)

lemma augmentation_epi [QuasiIso π] : Epi (π.f 0) :=
  epi_of_isColimit_cofork (augmentationIsCokernel π)

end CategoryTheory.Sheaf.ModuleCoefficients
