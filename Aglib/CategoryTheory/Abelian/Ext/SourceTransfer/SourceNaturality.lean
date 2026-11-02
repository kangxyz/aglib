/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.SourceTransfer

/-! # Source-square naturality of the original exact Ext transfer

An ordinary commuting square of source arrows compares the same exact
coefficient transfer, retaining independent source and target Ext universes.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Functor

universe u v u' v' e e'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{e} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{e'} D]

/-- Precomposition in an ordinary source square commutes with the unchanged
exact transfer and its actual coefficient arrow. -/
theorem extCoefficientTransfer_source_naturality
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {U₁ U₂ A : C} {V₁ V₂ B : D}
    (tU : U₂ ⟶ U₁) (tV : V₂ ⟶ V₁) (s₁ : V₁ ⟶ L.obj U₁) (s₂ : V₂ ⟶ L.obj U₂)
    (hs : tV ≫ s₁ = s₂ ≫ L.map tU) (φ : L.obj A ⟶ B)
    (n : ℕ) (x : Ext.{e} U₁ A n) :
    (Ext.mk₀ tV).comp (L.extCoefficientTransfer s₁ φ n x) (Nat.zero_add n) =
      L.extCoefficientTransfer s₂ φ n ((Ext.mk₀ tU).comp x (Nat.zero_add n)) := by
  change (Ext.mk₀ tV).comp
      (((Ext.mk₀ s₁).comp (x.mapExactFunctor L) (Nat.zero_add n)).comp
        (Ext.mk₀ φ) (Nat.add_zero n)) (Nat.zero_add n) =
    ((Ext.mk₀ s₂).comp
      (((Ext.mk₀ tU).comp x (Nat.zero_add n)).mapExactFunctor L)
      (Nat.zero_add n)).comp (Ext.mk₀ φ) (Nat.add_zero n)
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero, ← Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀]
  exact congrArg (fun k => ((Ext.mk₀ k).comp (x.mapExactFunctor L)
    (Nat.zero_add n)).comp (Ext.mk₀ φ) (Nat.add_zero n)) hs

end CategoryTheory.Functor
