/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.Bifunctor.Linear

/-! Native bilinearity retains all three independent Ext universes. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped TensorProduct

universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃ r

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

example {X₀ X₁ : C} {Y₀ Y₁ : D} {p q n : ℕ} (h : p + q = n)
    (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) :
    F.extBifunctorTensorMap (R := R) X₀ X₁ Y₀ Y₁ p q n h (x ⊗ₜ[R] y) =
      F.extBifunctor x y h :=
  F.extBifunctorTensorMap_tmul (R := R) h x y

example {X₀ X₁ : C} {Y₀ Y₁ : D} {U V : E}
    (s : U ⟶ (F.obj X₀).obj Y₀) (t : (F.obj X₁).obj Y₁ ⟶ V)
    {p q n : ℕ} (h : p + q = n) (x : Ext.{w₁} X₀ X₁ p) (y : Ext.{w₂} Y₀ Y₁ q) :
    F.extBifunctorLinearMapWithMaps (R := R) s t h x y =
      ((Ext.mk₀ s).comp (F.extBifunctor x y h) (Nat.zero_add n)).comp
        (Ext.mk₀ t) (Nat.add_zero n) :=
  F.extBifunctorLinearMapWithMaps_apply_apply (R := R) s t h x y
