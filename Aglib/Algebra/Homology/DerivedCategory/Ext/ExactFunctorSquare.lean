/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.CompositeComparison

/-! # Whole source-and-coefficient squares for original exact-functor Ext maps

This is assembly of the native natural-transformation law, retaining both
original source maps and coefficient arrows and independent Ext universes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory

universe u v u' v' e e'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{e} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{e'} D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The original Ext comparison commutes with a proved whole source/coefficient
square. No injective-preservation or acyclicity assumption is required. -/
theorem Functor.extPrecompMap_postcomp_eq_of_natTrans (τ : F ⟶ G)
    {A B : C} {A' B' : D} (a : A' ⟶ F.obj A) (b : A' ⟶ G.obj A)
    (c : F.obj B ⟶ B') (d : G.obj B ⟶ B')
    (hs : a ≫ τ.app A = b) (hc : τ.app B ≫ d = c)
    (n : ℕ) (x : Ext.{e} A B n) :
    (F.extPrecompMap a B n x).comp (Ext.mk₀ c) (Nat.add_zero n) =
      (G.extPrecompMap b B n x).comp (Ext.mk₀ d) (Nat.add_zero n) := by
  simp only [Functor.extPrecompMap_apply]
  calc
    _ = ((Ext.mk₀ a).comp
        ((x.mapExactFunctor F).comp (Ext.mk₀ (τ.app B)) (Nat.add_zero n))
          (Nat.zero_add n)).comp (Ext.mk₀ d) (Nat.add_zero n) := by
      simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, hc]
    _ = ((Ext.mk₀ a).comp
        ((Ext.mk₀ (τ.app A)).comp (x.mapExactFunctor G) (Nat.zero_add n))
          (Nat.zero_add n)).comp (Ext.mk₀ d) (Nat.add_zero n) := by
      rw [Ext.mapExactFunctor_comp_mk₀_natTransApp]
    _ = _ := by
      rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, hs]

end CategoryTheory
