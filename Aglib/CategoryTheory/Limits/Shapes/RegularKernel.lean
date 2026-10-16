/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Retract

/-!
# Additive functors preserve kernels of regular morphisms

An actual generalized inverse `s` with `f ≫ s ≫ f = f` gives the original
kernel a split inclusion. Its complementary projection is `1 - f ≫ s`.
Every additive functor preserves the resulting kernel universal property.
No abelian category, exact functor or preservation of other kernels is
assumed. The generalized inverse remains explicit data.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {X Y : C} (f : X ⟶ Y) (s : Y ⟶ X)

/-- The original kernel is a retract of the source, with complementary projection
`1 - f ≫ s`, for the displayed generalized inverse. -/
def kernelRetractOfGeneralizedInverse [HasKernel f] (hs : f ≫ s ≫ f = f) :
    Retract (kernel f) X := by
  have hz : (𝟙 X - f ≫ s) ≫ f = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hs, sub_self]
  let q : X ⟶ kernel f := kernel.lift f (𝟙 X - f ≫ s) hz
  have hq : q ≫ kernel.ι f = 𝟙 X - f ≫ s := kernel.lift_ι _ _ _
  have hkq : kernel.ι f ≫ q = 𝟙 _ := by
    apply (cancel_mono (kernel.ι f)).mp
    simp only [Category.assoc, hq, Preadditive.comp_sub, Category.comp_id,
      kernel.condition_assoc, zero_comp, sub_zero, Category.id_comp]
  exact { i := kernel.ι f, r := q, retract := hkq }

/-- The native kernel retraction retains its actual complementary projection. -/
@[reassoc]
theorem kernelRetractOfGeneralizedInverse_r_ι [HasKernel f] (hs : f ≫ s ≫ f = f) :
    (kernelRetractOfGeneralizedInverse f s hs).r ≫ kernel.ι f = 𝟙 X - f ≫ s :=
  kernel.lift_ι _ _ _

/-- The original source is a retract of its kernel plus its target. This uses the
displayed generalized inverse and the actual complementary kernel projection. -/
def sourceRetractOfGeneralizedInverse [HasKernel f] [HasBinaryBiproduct (kernel f) Y]
    (hs : f ≫ s ≫ f = f) : Retract X (kernel f ⊞ Y) := {
  i := biprod.lift (kernelRetractOfGeneralizedInverse f s hs).r f
  r := biprod.desc (kernel.ι f) s
  retract := by
    rw [biprod.lift_desc, kernelRetractOfGeneralizedInverse_r_ι]
    exact sub_add_cancel _ _ }

/-- Every additive functor preserves the original kernel of a morphism admitting the
displayed generalized inverse. Only existence of that kernel is required. -/
theorem preservesKernel_of_generalizedInverse [HasKernel f] (hs : f ≫ s ≫ f = f) :
    PreservesLimit (parallelPair f 0) F := by
  let r := kernelRetractOfGeneralizedInverse f s hs
  let q := r.r
  have hq : q ≫ kernel.ι f = 𝟙 X - f ≫ s :=
    kernelRetractOfGeneralizedInverse_r_ι f s hs
  have hkq : kernel.ι f ≫ q = 𝟙 _ := r.retract
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
  refine (KernelFork.isLimitMapConeEquiv
    (KernelFork.ofι (kernel.ι f) (kernel.condition f)) F).symm ?_
  refine KernelFork.IsLimit.ofι (F.map (kernel.ι f))
    (by rw [← F.map_comp, kernel.condition, F.map_zero])
    (fun {W} m hm => m ≫ F.map q) ?_ ?_
  · intro W m hm
    rw [Category.assoc, ← F.map_comp, hq, F.map_sub, F.map_id, F.map_comp,
      Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hm, zero_comp, sub_zero]
  · intro W m hm t ht
    simpa only [Category.assoc, ← F.map_comp, hkq, F.map_id, Category.comp_id] using
      congrArg (fun z => z ≫ F.map q) ht

end CategoryTheory.Limits
