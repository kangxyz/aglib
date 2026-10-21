/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.Cokernel
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# The degree-one tensor and dual comparison

Currying identifies the actual Hom cokernels of a short exact sequence and
its tensor sequence. When the original middle term is projective, this gives
an injection into degree-one Ext for the tensor sequence. Tensor exactness at
the left is an explicit hypothesis on the original map; the tensor middle
term is not assumed projective. The Ext universe remains independent.
-/

@[expose] public section

noncomputable section

universe u w

open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct

namespace ModuleCat

variable {R : Type u} [CommRing R]
    (L : Type u) [AddCommGroup L] [Module R L]

/-- Currying between the native categorical Hom modules. -/
def homDualTensorLinearEquiv (M : ModuleCat.{u} R) :
    (M ⟶ ModuleCat.of R (Module.Dual R L)) ≃ₗ[R]
      (ModuleCat.of R (M ⊗[R] L) ⟶ ModuleCat.of R R) :=
  (ModuleCat.homLinearEquiv (S := R) (M := M)
    (N := ModuleCat.of R (Module.Dual R L))).trans
    ((TensorProduct.lift.equiv (RingHom.id R) M L R).trans
      (ModuleCat.homLinearEquiv (S := R) (M := ModuleCat.of R (M ⊗[R] L))
        (N := ModuleCat.of R R)).symm)

/-- Currying intertwines restriction with the original tensor map. -/
theorem homDualTensorLinearEquiv_comp {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (homDualTensorLinearEquiv L M).toLinearMap.comp
        (CategoryTheory.Linear.leftComp R (ModuleCat.of R (Module.Dual R L)) f) =
      (CategoryTheory.Linear.leftComp R (ModuleCat.of R R)
        (ModuleCat.ofHom (f.hom.rTensor L))).comp
          (homDualTensorLinearEquiv L N).toLinearMap := by
  ext φ m l
  rfl

/-- The actual short complex obtained by tensoring on the right. -/
def rTensorShortComplex (S : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (S.f.hom.rTensor L) (S.g.hom.rTensor L) (by
    rw [← LinearMap.rTensor_comp]
    have hzero : S.g.hom.comp S.f.hom = 0 := congrArg ModuleCat.Hom.hom S.zero
    rw [hzero, LinearMap.rTensor_zero])

/-- Right exactness and the stated injectivity give the actual tensor short
exact sequence. -/
theorem rTensorShortComplex_shortExact {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (hf : Function.Injective (S.f.hom.rTensor L)) :
    (rTensorShortComplex L S).ShortExact := by
  have hex : Function.Exact S.f.hom S.g.hom := by
    rw [LinearMap.exact_iff]
    exact hS.exact.moduleCat_range_eq_ker.symm
  exact ModuleCat.shortComplex_shortExact _
    (_root_.rTensor_exact L hex hS.moduleCat_surjective_g) hf
    (LinearMap.rTensor_surjective L hS.moduleCat_surjective_g)

/-- Currying identifies the two native Hom cokernels, with the original
restriction maps on both sides. -/
def homCokernelDualTensorLinearEquiv (S : ShortComplex (ModuleCat.{u} R)) :
    ((S.X₁ ⟶ ModuleCat.of R (Module.Dual R L)) ⧸
      LinearMap.range (CategoryTheory.Linear.leftComp R
        (ModuleCat.of R (Module.Dual R L)) S.f)) ≃ₗ[R]
    (((rTensorShortComplex L S).X₁ ⟶ ModuleCat.of R R) ⧸
      LinearMap.range (CategoryTheory.Linear.leftComp R
        (ModuleCat.of R R) (rTensorShortComplex L S).f)) :=
  Submodule.Quotient.equiv _ _ (homDualTensorLinearEquiv L S.X₁) (by
    rw [← LinearMap.range_comp]
    exact (congrArg LinearMap.range (homDualTensorLinearEquiv_comp L S.f)).trans
      (LinearMap.range_comp_of_range_eq_top _
        (homDualTensorLinearEquiv L S.X₂).range))

variable [HasExt.{w} (ModuleCat.{u} R)]

/-- The degree-one tensor/Hom comparison uses a projective original middle
term and only injectivity for the tensor connecting cokernel. -/
def extOneDualTensorLinearMap {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) [Projective S.X₂]
    (hf : Function.Injective (S.f.hom.rTensor L)) :
    Ext.{w} S.X₃ (ModuleCat.of R (Module.Dual R L)) 1 →ₗ[R]
      Ext.{w} (ModuleCat.of R (S.X₃ ⊗[R] L)) (ModuleCat.of R R) 1 :=
  ((rTensorShortComplex_shortExact L hS hf).homCokernelExtOneLinearMap
    (R := R) (ModuleCat.of R R)).comp
      ((homCokernelDualTensorLinearEquiv L S).toLinearMap.comp
        (hS.homCokernelExtOneLinearEquiv (R := R)
          (ModuleCat.of R (Module.Dual R L))).symm.toLinearMap)

/-- The comparison is injective; surjectivity is deliberately not asserted. -/
theorem extOneDualTensorLinearMap_injective {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) [Projective S.X₂]
    (hf : Function.Injective (S.f.hom.rTensor L)) :
    Function.Injective (extOneDualTensorLinearMap L hS hf) :=
  ((rTensorShortComplex_shortExact L hS hf).homCokernelExtOneLinearMap_injective
    (R := R) (ModuleCat.of R R)).comp
      ((homCokernelDualTensorLinearEquiv L S).injective.comp
        (hS.homCokernelExtOneLinearEquiv (R := R)
          (ModuleCat.of R (Module.Dual R L))).symm.injective)

end ModuleCat
