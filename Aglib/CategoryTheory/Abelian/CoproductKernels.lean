/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Original kernels of coproduct maps in an AB4 category -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Limits
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type w} [HasCoproducts.{w} C] [AB4OfSize.{w} C]
  {P Q : ι → C} (f : ∀ i, P i ⟶ Q i)

/-- The actual component kernels form a kernel fork in the discrete diagram category. -/
def discreteKernelFork : KernelFork (Discrete.natTrans (fun i => f i.as) :
      Discrete.functor P ⟶ Discrete.functor Q) :=
  KernelFork.ofι (Discrete.natTrans (fun i => kernel.ι (f i.as)) :
    Discrete.functor (fun i => kernel (f i)) ⟶ Discrete.functor P) (by
    ext i
    exact kernel.condition (f i.as))

/-- The kernel fork of the original discrete diagram is limiting. -/
def discreteKernelForkIsLimit : IsLimit (discreteKernelFork f) := by
  apply evaluationJointlyReflectsLimits
  intro i
  exact ((discreteKernelFork f).isLimitMapConeEquiv ((evaluation _ C).obj i)).symm
    (kernelIsKernel (f i.as))

/-- Exactness of coproducts preserves the literal component kernel inclusions. -/
def coproductKernelForkIsLimit :
    IsLimit (KernelFork.ofι (Sigma.map (fun i => kernel.ι (f i)))
      (by apply Sigma.hom_ext; intro i; simp) : KernelFork (Sigma.map f)) :=
  (discreteKernelFork f).mapIsLimit (discreteKernelForkIsLimit f) colim

/-- The coproduct of component kernels is the kernel of the original coproduct map. -/
def coproductKernelIso : (∐ fun i => kernel (f i)) ≅ kernel (Sigma.map f) :=
  (coproductKernelForkIsLimit f).conePointUniqueUpToIso
    (limit.isLimit (parallelPair (Sigma.map f) 0))

/-- The comparison retains the original coproduct kernel inclusion. -/
@[reassoc (attr := simp)]
theorem coproductKernelIso_hom_ι :
    (coproductKernelIso f).hom ≫ kernel.ι (Sigma.map f) =
      Sigma.map (fun i => kernel.ι (f i)) :=
  (coproductKernelForkIsLimit f).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (parallelPair (Sigma.map f) 0)) WalkingParallelPair.zero

end CategoryTheory.Limits
