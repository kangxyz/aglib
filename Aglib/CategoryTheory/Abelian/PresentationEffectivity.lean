/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Effectivity of two-term presentations

A full functor preserving cokernels algebraizes every object presented by two
objects in its image: lift the relation map and take its original cokernel.
The comparison retains the original quotient arrow. This is a categorical
supplier, not an assertion that such presentations exist in a geometric
application.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] (F : C ⥤ D) [F.Full]
  [F.PreservesZeroMorphisms] [PreservesFiniteColimits F]

/-- Lift the actual relation map, then compare its original cokernel with
the displayed quotient. No faithfulness assumption is needed for existence. -/
def presentationCokernelIso {P Q : C} {N : D}
    (r : F.obj P ⟶ F.obj Q) (π : F.obj Q ⟶ N) (w : r ≫ π = 0)
    (hex : (ShortComplex.mk r π w).Exact) [Epi π] :
    F.obj (cokernel (F.preimage r)) ≅ N :=
  PreservesCokernel.iso F (F.preimage r) ≪≫
    cokernelIsoOfEq (F.map_preimage r) ≪≫
      IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel r) hex.gIsCokernel

/-- The effectivity comparison identifies the original quotient arrow. -/
@[reassoc (attr := simp)]
theorem presentationCokernelIso_π {P Q : C} {N : D}
    (r : F.obj P ⟶ F.obj Q) (π : F.obj Q ⟶ N) (w : r ≫ π = 0)
    (hex : (ShortComplex.mk r π w).Exact) [Epi π] :
    F.map (cokernel.π (F.preimage r)) ≫
      (presentationCokernelIso F r π w hex).hom = π := by
  simp only [presentationCokernelIso, Iso.trans_hom, ← Category.assoc,
    PreservesCokernel.π_iso_hom, π_comp_cokernelIsoOfEq_hom]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel r) hex.gIsCokernel WalkingParallelPair.one

/-- Every object with a two-term presentation by actual image objects lies
in the essential image, with the original algebraic cokernel as witness. -/
theorem essImage_of_presentation {P Q : C} {N : D}
    (r : F.obj P ⟶ F.obj Q) (π : F.obj Q ⟶ N) (w : r ≫ π = 0)
    (hex : (ShortComplex.mk r π w).Exact) [Epi π] : F.essImage N :=
  ⟨cokernel (F.preimage r), ⟨presentationCokernelIso F r π w hex⟩⟩

/-- Covering an object and its actual kernel by image objects supplies the
required two-term presentation. This uses the categorical kernel, not an
assumed levelwise kernel in a category of compatible systems. -/
theorem essImage_of_epi_of_kernel_epi {Q P : C} {N : D}
    (π : F.obj Q ⟶ N) [Epi π]
    (r : F.obj P ⟶ kernel π) [Epi r] : F.essImage N := by
  let S := ShortComplex.mk (r ≫ kernel.ι π) π (by simp)
  have he : kernel.lift π S.f S.zero = r := by
    apply (cancel_mono (kernel.ι π)).mp
    simp [S]
  have hS : S.Exact := S.exact_iff_epi_kernel_lift.mpr (by rw [he]; infer_instance)
  exact essImage_of_presentation F S.f π S.zero hS

end CategoryTheory.Functor
