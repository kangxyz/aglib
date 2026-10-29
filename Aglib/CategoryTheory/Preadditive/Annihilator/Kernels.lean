/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Native scalar kernels and their products

Maps from objects killed by a natural number factor through the actual scalar
kernel. Additive left exact functors transport that same kernel through the
native preserved-kernel comparison. The scalar kernel of an actual product is
the actual product of its scalar kernels, with the original projections and
kernel inclusions. Only the displayed kernels and products are required.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Preadditive

universe uC uD vC vD w

variable {C : Type uC} [Category.{vC} C] [Preadditive C]

/-- A map from an actually killed source factors through the original scalar kernel. -/
def killedKernelLift {A B : C} (n : ℕ) [HasKernel (n • 𝟙 B)]
    (hA : n • 𝟙 A = 0) (a : A ⟶ B) : A ⟶ kernel (n • 𝟙 B) :=
  kernel.lift (n • 𝟙 B) a (by
    calc
      a ≫ (n • 𝟙 B) = n • a := by rw [comp_nsmul, Category.comp_id]
      _ = (n • 𝟙 A) ≫ a := by rw [nsmul_comp, Category.id_comp]
      _ = 0 := by rw [hA, zero_comp])

/-- The scalar-kernel lift recovers the literal original arrow. -/
@[reassoc]
theorem killedKernelLift_ι {A B : C} (n : ℕ) [HasKernel (n • 𝟙 B)]
    (hA : n • 𝟙 A = 0) (a : A ⟶ B) :
    killedKernelLift n hA a ≫ kernel.ι (n • 𝟙 B) = a :=
  kernel.lift_ι _ _ _

/-- The actual scalar kernel is itself killed by the same scalar. -/
theorem nsmul_id_kernel (A : C) (n : ℕ) [HasKernel (n • 𝟙 A)] :
    n • 𝟙 (kernel (n • 𝟙 A)) = 0 := by
  apply (cancel_mono (kernel.ι (n • 𝟙 A))).mp
  simpa only [nsmul_comp, Category.id_comp, comp_nsmul, Category.comp_id,
    zero_comp] using kernel.condition (n • 𝟙 A)

section Preservation

variable {D : Type uD} [Category.{vD} D] [Preadditive D]

/-- An additive left exact functor preserves the actual scalar kernel. -/
def nsmulKernelIso (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (A : C) (n : ℕ) [HasKernel (n • 𝟙 A)] [HasKernel (n • 𝟙 (F.obj A))] :
    F.obj (kernel (n • 𝟙 A)) ≅ kernel (n • 𝟙 (F.obj A)) :=
  PreservesKernel.iso F (n • 𝟙 A) ≪≫
    kernelIsoOfEq (f := F.map (n • 𝟙 A)) (g := n • 𝟙 (F.obj A))
      (by rw [Functor.map_nsmul, Functor.map_id])

/-- The inverse comparison retains the original mapped kernel inclusion. -/
@[reassoc]
theorem nsmulKernelIso_inv_ι
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (A : C) (n : ℕ)
    [HasKernel (n • 𝟙 A)] [HasKernel (n • 𝟙 (F.obj A))] :
    (nsmulKernelIso F A n).inv ≫ F.map (kernel.ι (n • 𝟙 A)) =
      kernel.ι (n • 𝟙 (F.obj A)) := by
  simp only [nsmulKernelIso, Iso.trans_inv, Category.assoc,
    PreservesKernel.iso_inv_ι, kernelIsoOfEq_inv_comp_ι]

end Preservation

section Products

variable (n : ℕ) {I : Type w} (G : I → C) [∀ i, HasKernel (n • 𝟙 (G i))]

/-- The original coordinate scalar kernels, indexed by the original type. -/
abbrev nsmulKernelProductFamily : I → C := fun i => kernel (n • 𝟙 (G i))

variable [HasProduct (nsmulKernelProductFamily n G)]

/-- The actual product of coordinate scalar kernels is killed by the scalar. -/
theorem nsmulKernelProduct_nsmul_id :
    n • 𝟙 (∏ᶜ nsmulKernelProductFamily n G) = 0 := by
  apply Pi.hom_ext
  intro i
  have hi : n • 𝟙 (nsmulKernelProductFamily n G i) = 0 := nsmul_id_kernel (G i) n
  calc
    _ = Pi.π (nsmulKernelProductFamily n G) i ≫
        (n • 𝟙 (nsmulKernelProductFamily n G i)) := by
      simp only [nsmul_comp, Category.id_comp, comp_nsmul, Category.comp_id]
    _ = 0 := by rw [hi, comp_zero]
    _ = _ := by rw [zero_comp]

variable [HasProduct G]

/-- The actual product of the original scalar-kernel inclusions. -/
def nsmulKernelProductInclusion :
    (∏ᶜ nsmulKernelProductFamily n G) ⟶ ∏ᶜ G :=
  Limits.Pi.map (f := nsmulKernelProductFamily n G) (g := G)
    fun i => kernel.ι (n • 𝟙 (G i))

private theorem nsmulKernelProductInclusion_π (i : I) :
    nsmulKernelProductInclusion n G ≫ Pi.π G i =
      Pi.π (nsmulKernelProductFamily n G) i ≫ kernel.ι (n • 𝟙 (G i)) :=
  Pi.map_π (f := nsmulKernelProductFamily n G) (g := G)
    (fun j => kernel.ι (n • 𝟙 (G j))) i

instance nsmulKernelProductInclusion_mono : Mono (nsmulKernelProductInclusion n G) := by
  refine ⟨fun {Z} a b h => ?_⟩
  apply Pi.hom_ext
  intro i
  apply (cancel_mono (kernel.ι (n • 𝟙 (G i)))).mp
  have hπ := congrArg (fun q : Z ⟶ ∏ᶜ G => q ≫ Pi.π G i) h
  simpa only [Category.assoc, nsmulKernelProductInclusion_π] using hπ

variable [HasKernel (n • 𝟙 (∏ᶜ G))]

/-- Original product projections induce the native coordinate kernel maps. -/
def nsmulKernelProductForward :
    kernel (n • 𝟙 (∏ᶜ G)) ⟶ ∏ᶜ nsmulKernelProductFamily n G :=
  Pi.lift (f := nsmulKernelProductFamily n G)
    fun i => kernel.map (n • 𝟙 (∏ᶜ G)) (n • 𝟙 (G i))
    (Pi.π G i) (Pi.π G i) (by
      simp only [nsmul_comp, Category.id_comp, comp_nsmul, Category.comp_id])

/-- Every forward coordinate retains its original projection and kernel inclusions. -/
@[reassoc]
theorem nsmulKernelProductForward_π_ι (i : I) :
    nsmulKernelProductForward n G ≫ Pi.π (nsmulKernelProductFamily n G) i ≫
        kernel.ι (n • 𝟙 (G i)) =
      kernel.ι (n • 𝟙 (∏ᶜ G)) ≫ Pi.π G i := by
  have hπ : nsmulKernelProductForward n G ≫ Pi.π (nsmulKernelProductFamily n G) i =
      kernel.map (n • 𝟙 (∏ᶜ G)) (n • 𝟙 (G i)) (Pi.π G i) (Pi.π G i) (by
        simp only [nsmul_comp, Category.id_comp, comp_nsmul, Category.comp_id]) := by
    unfold nsmulKernelProductForward
    exact Pi.lift_comp_π (f := nsmulKernelProductFamily n G) _ i
  calc
    _ = (nsmulKernelProductForward n G ≫ Pi.π (nsmulKernelProductFamily n G) i) ≫
        kernel.ι (n • 𝟙 (G i)) := (Category.assoc _ _ _).symm
    _ = _ := (congrArg (fun q : kernel (n • 𝟙 (∏ᶜ G)) ⟶ kernel (n • 𝟙 (G i)) =>
      q ≫ kernel.ι (n • 𝟙 (G i))) hπ).trans (kernel.lift_ι _ _ _)

/-- The actual product of inclusions factors through the original scalar kernel. -/
def nsmulKernelProductBackward :
    (∏ᶜ nsmulKernelProductFamily n G) ⟶ kernel (n • 𝟙 (∏ᶜ G)) :=
  killedKernelLift n (nsmulKernelProduct_nsmul_id n G)
    (nsmulKernelProductInclusion n G)

/-- The forward map retains the original product of kernel inclusions. -/
@[reassoc]
theorem nsmulKernelProductForward_inclusion :
    nsmulKernelProductForward n G ≫ nsmulKernelProductInclusion n G =
      kernel.ι (n • 𝟙 (∏ᶜ G)) := by
  apply Pi.hom_ext
  intro i
  calc
    _ = nsmulKernelProductForward n G ≫
        (nsmulKernelProductInclusion n G ≫ Pi.π G i) := Category.assoc _ _ _
    _ = nsmulKernelProductForward n G ≫
        (Pi.π (nsmulKernelProductFamily n G) i ≫ kernel.ι (n • 𝟙 (G i))) :=
      congrArg (fun q : (∏ᶜ nsmulKernelProductFamily n G) ⟶ G i =>
        nsmulKernelProductForward n G ≫ q) (nsmulKernelProductInclusion_π n G i)
    _ = _ := nsmulKernelProductForward_π_ι n G i

/-- The backward map retains the literal product of original inclusions. -/
@[reassoc]
theorem nsmulKernelProductBackward_inclusion :
    nsmulKernelProductBackward n G ≫ kernel.ι (n • 𝟙 (∏ᶜ G)) =
      nsmulKernelProductInclusion n G :=
  killedKernelLift_ι _ _ _

/-- The scalar kernel of the actual product is the product of its actual scalar kernels. -/
def nsmulKernelProductIso :
    kernel (n • 𝟙 (∏ᶜ G)) ≅ ∏ᶜ nsmulKernelProductFamily n G where
  hom := nsmulKernelProductForward n G
  inv := nsmulKernelProductBackward n G
  hom_inv_id := by
    apply (cancel_mono (kernel.ι (n • 𝟙 (∏ᶜ G)))).mp
    rw [Category.assoc, nsmulKernelProductBackward_inclusion,
      nsmulKernelProductForward_inclusion, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (nsmulKernelProductInclusion n G)).mp
    rw [Category.assoc, nsmulKernelProductForward_inclusion,
      nsmulKernelProductBackward_inclusion, Category.id_comp]

end Products

end CategoryTheory.Preadditive
