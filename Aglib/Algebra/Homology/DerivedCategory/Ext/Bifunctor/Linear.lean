/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.Bifunctor
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Linearity of the original external Ext pairing

The two original exact-functor maps and original Ext composition form a
bilinear map over any commutative structural scalar ring. All three Ext
worlds stay independent. Source and coefficient arrows are incorporated in
one whole bilinear constructor before individual classes are evaluated.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped TensorProduct

universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃ r

namespace CategoryTheory.Functor

variable {R : Type r} [CommRing R]
  {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C] [CategoryTheory.Linear R C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w₂} D] [CategoryTheory.Linear R D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w₃} E] [CategoryTheory.Linear R E]
  (F : C ⥤ D ⥤ E) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ X, PreservesFiniteLimits (F.obj X)] [∀ X, PreservesFiniteColimits (F.obj X)]
  [∀ Y, PreservesFiniteLimits (F.flip.obj Y)]
  [∀ Y, PreservesFiniteColimits (F.flip.obj Y)]
  [∀ X, (F.obj X).Linear R] [∀ Y, (F.flip.obj Y).Linear R]

local instance (Y : D) : (F.flip.obj Y).Additive := { }

/-- The bilinear upgrade of the original external Ext map, using precisely
its original exact-functor maps and composition. -/
def extBifunctorLinearMap (X₀ X₁ : C) (Y₀ Y₁ : D) (p q n : ℕ) (h : p + q = n) :
    Ext.{w₁} X₀ X₁ p →ₗ[R]
      Ext.{w₂} Y₀ Y₁ q →ₗ[R] Ext.{w₃} ((F.obj X₀).obj Y₀) ((F.obj X₁).obj Y₁) n :=
  ((Ext.bilinearCompOfLinear R ((F.obj X₀).obj Y₀) ((F.obj X₁).obj Y₀)
    ((F.obj X₁).obj Y₁) p q n h).compl₂ ((F.obj X₁).mapExtLinearMap R Y₀ Y₁ q)).comp
      ((F.flip.obj Y₀).mapExtLinearMap R X₀ X₁ p)

/-- The forward pairing is the original external Ext operator. -/
@[simp]
theorem extBifunctorLinearMap_apply_apply {X₀ X₁ : C} {Y₀ Y₁ : D}
    {p q n : ℕ} (h : p + q = n) (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) :
    F.extBifunctorLinearMap (R := R) X₀ X₁ Y₀ Y₁ p q n h x y = F.extBifunctor x y h := rfl

/-- The original external pairing with actual source and coefficient maps,
constructed as a whole bilinear map on the same original Ext groups. -/
def extBifunctorLinearMapWithMaps {X₀ X₁ : C} {Y₀ Y₁ : D} {U V : E}
    (s : U ⟶ (F.obj X₀).obj Y₀) (t : (F.obj X₁).obj Y₁ ⟶ V)
    {p q n : ℕ} (h : p + q = n) :
    Ext.{w₁} X₀ X₁ p →ₗ[R] Ext.{w₂} Y₀ Y₁ q →ₗ[R] Ext.{w₃} U V n :=
  (F.extBifunctorLinearMap (R := R) X₀ X₁ Y₀ Y₁ p q n h).compr₂
    ((Ext.postcompOfLinear (Ext.mk₀ t) R U (Nat.add_zero n)).comp
      (Ext.precompOfLinear (Ext.mk₀ s) R ((F.obj X₁).obj Y₁) (Nat.zero_add n)))

/-- Its forward value is precisely the original pairing followed by the two
original degree-zero Ext compositions. -/
@[simp]
theorem extBifunctorLinearMapWithMaps_apply_apply
    {X₀ X₁ : C} {Y₀ Y₁ : D} {U V : E}
    (s : U ⟶ (F.obj X₀).obj Y₀) (t : (F.obj X₁).obj Y₁ ⟶ V)
    {p q n : ℕ} (h : p + q = n) (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) :
    F.extBifunctorLinearMapWithMaps (R := R) s t h x y =
      ((Ext.mk₀ s).comp (F.extBifunctor x y h) (Nat.zero_add n)).comp
        (Ext.mk₀ t) (Nat.add_zero n) := rfl

/-- The original external pairing on the actual tensor of the two Ext groups. -/
def extBifunctorTensorMap (X₀ X₁ : C) (Y₀ Y₁ : D) (p q n : ℕ) (h : p + q = n) :
    Ext.{w₁} X₀ X₁ p ⊗[R] Ext.{w₂} Y₀ Y₁ q →ₗ[R]
      Ext.{w₃} ((F.obj X₀).obj Y₀) ((F.obj X₁).obj Y₁) n :=
  TensorProduct.lift (F.extBifunctorLinearMap (R := R) X₀ X₁ Y₀ Y₁ p q n h)

@[simp]
theorem extBifunctorTensorMap_tmul {X₀ X₁ : C} {Y₀ Y₁ : D}
    {p q n : ℕ} (h : p + q = n) (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) :
    F.extBifunctorTensorMap (R := R) X₀ X₁ Y₀ Y₁ p q n h (x ⊗ₜ[R] y) =
      F.extBifunctor x y h := rfl

end CategoryTheory.Functor
