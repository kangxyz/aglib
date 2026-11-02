/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel
public import Aglib.AlgebraicGeometry.Group.Kernel.Basic

/-!
# The represented sheaf of the native scheme kernel

The original group-object pullback supplies the kernel inclusion and every Over-section lift.
Pointwise multiplication by a natural number induces the corresponding additive sheaf scalar.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open CategoryTheory.Functor.LargePresheaf
attribute [local instance] AlgebraicGeometry.Scheme.EtaleCohomology.hasSheafifyLarge

namespace AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel.Native

universe u
attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{u}} {G E : Grp (Over S)}

instance inclusion_mono (p : G ⟶ E) : Mono (Group.Kernel.inclusion p).hom.hom :=
  (Group.Kernel.square p).mono_fst_of_mono

instance kernel_comm (p : G ⟶ E) [IsCommMonObj G.X] :
    IsCommMonObj (Group.Kernel.group p).X := by
  rw [isCommMonObj_iff_isMulCommutative]
  intro V
  refine ⟨⟨fun a b => ?_⟩⟩
  apply (cancel_mono (Group.Kernel.inclusion p).hom.hom).mp
  rw [MonObj.mul_comp, MonObj.mul_comp, mul_comm]

/-- The original pullback inclusion has zero composite as a group morphism. -/
theorem inclusion_comp (p : G ⟶ E) : Group.Kernel.inclusion p ≫ p = 0 := by
  apply (Grp.forget (Over S)).map_injective
  change (Group.Kernel.inclusion p).hom.hom ≫ p.hom.hom = 1
  exact (Group.Kernel.square p).w

variable (p : G ⟶ E) [IsCommMonObj G.X] [IsCommMonObj E.X]

/-- The actual scheme pullback represents the sheaf kernel. -/
def kernelIsLimit :
    IsLimit (KernelFork.ofι (representedSheafMap (Group.Kernel.inclusion p))
      (represented_composition_zero (Group.Kernel.inclusion p) p (inclusion_comp p))) :=
  representedKernelIsLimit (Group.Kernel.inclusion p) p
    (fun x h => (Group.Kernel.square p).lift x (toUnit _) h)
    (fun x h => (Group.Kernel.square p).lift_fst x (toUnit _) h)
    (inclusion_comp p)

/-- Kernel uniqueness compares the original represented group with the categorical kernel. -/
def kernelIso :
    representedSheaf (Group.Kernel.group p) ≅ kernel (representedSheafMap p) := by
  let e := (kernelIsLimit p).conePointUniqueUpToIso
    (kernelIsKernel (representedSheafMap p))
  exact e

/-- This comparison preserves the original insertion, not only the kernel objects. -/
@[reassoc (attr := simp)]
theorem kernelIso_hom_ι :
    (kernelIso p).hom ≫ kernel.ι (representedSheafMap p) =
      representedSheafMap (Group.Kernel.inclusion p) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (kernelIsLimit p)
    (kernelIsKernel (representedSheafMap p)) WalkingParallelPair.zero

/-- The power in group morphisms is pointwise multiplication, not composition in `End`. -/
theorem representedSheafMap_multiplication (G : Grp (Over S)) [IsCommMonObj G.X]
    (n : ℕ) : representedSheafMap ((𝟙 G : G ⟶ G) ^ n) =
      n • 𝟙 (representedSheaf G) := by
  ext U x
  apply ULift.ext
  change Additive.ofMul (x.down.toMul ≫ (((𝟙 G : G ⟶ G) ^ n).hom.hom)) =
    n • x.down
  have hp : (((𝟙 G : G ⟶ G) ^ n).hom.hom) = (𝟙 G.X) ^ n := by
    simp only [Grp.Hom.hom_pow, Mon.Hom.hom_pow]
    rfl
  rw [hp, MonObj.comp_pow, Category.comp_id]
  rfl

/-- The native multiplication kernel represents the literal additive torsion kernel. -/
def multiplicationKernelIso (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℕ) :
    representedSheaf (Group.Kernel.group ((𝟙 G : G ⟶ G) ^ n)) ≅
      kernel (n • 𝟙 (representedSheaf G)) :=
  kernelIso ((𝟙 G : G ⟶ G) ^ n) ≪≫
    kernelIsoOfEq (representedSheafMap_multiplication G n)

end AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel.Native
