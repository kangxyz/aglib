/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Coefficients.ModuleCohomologyPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ZModLinear
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.DirectSum.Module

/-! The original ordered external product of constant module-unit Ext classes. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped TensorProduct DirectSum

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wX wY wZ

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule

variable (n : ℕ)

/-- Ext of the original module unit with itself. -/
abbrev constantModuleExt (X : Scheme.{u})
    [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))] (p : ℕ) :=
  Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod n))) (moduleUnit X (ULift.{u + 1} (ZMod n))) p

/-- Original module-unit pullback, with the original unit comparison also in the target. -/
@[no_expose]
def constantModuleExtPullback {X Z : Scheme.{u}} (f : Z ⟶ X)
    [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wZ} (ModuleSheaf Z (ULift.{u + 1} (ZMod n)))] (p : ℕ) :
    constantModuleExt.{u, wX} n X p →+ constantModuleExt.{u, wZ} n Z p :=
  ((Ext.mk₀ (moduleUnitInverseImageIso f n).hom).postcomp (moduleUnit Z (ULift.{u + 1} (ZMod n)))
    (add_zero p)).comp (moduleUnitExtPullback f n (moduleUnit X (ULift.{u + 1} (ZMod n))) p)

/-- The original Ext pullback uses the two original degree-zero unit comparisons. -/
theorem constantModuleExtPullback_apply {X Z : Scheme.{u}} (f : Z ⟶ X)
    [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wZ} (ModuleSheaf Z (ULift.{u + 1} (ZMod n)))]
    (p : ℕ) (x : constantModuleExt.{u, wX} n X p) :
    constantModuleExtPullback.{u, wX, wZ} n f p x =
      ((Ext.mk₀ (moduleUnitInverseImageIso f n).inv).comp
        (x.mapExactFunctor (moduleInverseImage f (ULift.{u + 1} (ZMod n)))) (zero_add p)).comp
          (Ext.mk₀ (moduleUnitInverseImageIso f n).hom) (add_zero p) := by
  unfold constantModuleExtPullback
  rw [AddMonoidHom.comp_apply, moduleUnitExtPullback_apply]
  rfl

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
  [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wY} (ModuleSheaf Y (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wZ} (ModuleSheaf (pullback f g) (ULift.{u + 1} (ZMod n)))]

/-- The original external product pulls both classes back along their actual
projections and composes them in the specified order. -/
@[no_expose]
def constantModuleExtExternalProduct (p q d : ℕ) (hd : p + q = d) :
    constantModuleExt.{u, wX} n X p →ₗ[ZMod n]
      constantModuleExt.{u, wY} n Y q →ₗ[ZMod n] constantModuleExt.{u, wZ} n (pullback f g) d := by
  let Z := pullback f g
  let I := moduleUnit Z (ULift.{u + 1} (ZMod n))
  let a := constantModuleExtPullback.{u, wX, wZ} n (pullback.fst f g) p
  let b := constantModuleExtPullback.{u, wY, wZ} n (pullback.snd f g) q
  let c := ((Ext.bilinearComp I I I p q d hd).comp a).compl₂ b
  exact ((AddMonoidHom.toZModLinearMapEquiv n).toAddMonoidHom.comp c).toZModLinearMap n

/-- Total-degree Künneth map from the original ordered external products. -/
@[no_expose]
def constantModuleExtKunnethMap (d : ℕ) :
    (⨁ p : Fin (d + 1), constantModuleExt.{u, wX} n X p.val ⊗[ZMod n]
      constantModuleExt.{u, wY} n Y (d - p.val)) →ₗ[ZMod n]
        constantModuleExt.{u, wZ} n (pullback f g) d :=
  DirectSum.toModule (ZMod n) _ _ (fun p =>
    TensorProduct.lift (constantModuleExtExternalProduct n f g p.val (d - p.val) d (by omega)))

/-- The original bilinear product on classes is their ordered Yoneda product. -/
theorem constantModuleExtExternalProduct_apply (p q d : ℕ) (hd : p + q = d)
    (a : constantModuleExt.{u, wX} n X p) (b : constantModuleExt.{u, wY} n Y q) :
    constantModuleExtExternalProduct n f g p q d hd a b =
      (constantModuleExtPullback.{u, wX, wZ} n (pullback.fst f g) p a).comp
        (constantModuleExtPullback.{u, wY, wZ} n (pullback.snd f g) q b) hd := by
  unfold constantModuleExtExternalProduct
  rfl

/-- On a pure tensor in its original graded summand, the Künneth map is the
original ordered product. -/
theorem constantModuleExtKunnethMap_lof_tmul (d : ℕ) (p : Fin (d + 1))
    (a : constantModuleExt.{u, wX} n X p.val)
    (b : constantModuleExt.{u, wY} n Y (d - p.val)) :
    constantModuleExtKunnethMap n f g d
      (DirectSum.lof (ZMod n) (Fin (d + 1))
        (fun i => constantModuleExt.{u, wX} n X i.val ⊗[ZMod n]
          constantModuleExt.{u, wY} n Y (d - i.val)) p (a ⊗ₜ b)) =
      constantModuleExtExternalProduct n f g p.val (d - p.val) d (by omega) a b := by
  unfold constantModuleExtKunnethMap
  rw [DirectSum.toModule_lof, TensorProduct.lift.tmul]

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
