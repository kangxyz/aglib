/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.SourceTransfer

/-! # Ordinary coefficient squares on exact Ext transfers

One selected composite functor, its actual source arrows and factorization
comparisons, and the ordinary coefficient equation determine the complete square.
All four Ext worlds remain
independent, and the proof uses only the original exact Ext maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Functor

universe u₀ v₀ e₀ u₁ v₁ e₁ u₂ v₂ e₂ u₃ v₃ e₃

variable {C₀ : Type u₀} [Category.{v₀} C₀] [Abelian C₀] [HasExt.{e₀} C₀]
  {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasExt.{e₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasExt.{e₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasExt.{e₃} C₃]

/-- Both actual paths factor through one selected composite exact functor.
The original source and coefficient equations determine its complete Ext value. -/
theorem extCoefficientTransfer_square
    (F₁ : C₀ ⥤ C₁) (F₂ : C₁ ⥤ C₃) (G₁ : C₀ ⥤ C₂) (G₂ : C₂ ⥤ C₃)
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (L₀ : C₀ ⥤ C₃) [L₀.Additive]
    [PreservesFiniteLimits L₀] [PreservesFiniteColimits L₀]
    (c : L₀ ≅ F₁ ⋙ F₂) (d : L₀ ≅ G₁ ⋙ G₂)
    {U₀ : C₀} {U₁ : C₁} {U₂ : C₂} {U₃ : C₃}
    (s₁ : U₁ ⟶ F₁.obj U₀) (s₂ : U₃ ⟶ F₂.obj U₁)
    (t₁ : U₂ ⟶ G₁.obj U₀) (t₂ : U₃ ⟶ G₂.obj U₂)
    (s₀ : U₃ ⟶ L₀.obj U₀)
    (hs : s₀ ≫ c.hom.app U₀ = s₂ ≫ F₂.map s₁)
    (ht : s₀ ≫ d.hom.app U₀ = t₂ ≫ G₂.map t₁)
    {A : C₀} {B : C₁} {C : C₂} {D : C₃}
    (α : F₁.obj A ⟶ B) (β : F₂.obj B ⟶ D)
    (γ : G₁.obj A ⟶ C) (δ : G₂.obj C ⟶ D)
    (hc : c.hom.app A ≫ F₂.map α ≫ β = d.hom.app A ≫ G₂.map γ ≫ δ)
    (q : ℕ) (x : Ext U₀ A q) :
    (F₂.extPrecompMap s₂ B q
      ((F₁.extPrecompMap s₁ A q x).comp (Ext.mk₀ α) (add_zero q))).comp
        (Ext.mk₀ β) (add_zero q) =
      (G₂.extPrecompMap t₂ C q
        ((G₁.extPrecompMap t₁ A q x).comp (Ext.mk₀ γ) (add_zero q))).comp
          (Ext.mk₀ δ) (add_zero q) := by
  have hleft := extCoefficientTransfer_comp F₁ F₂ L₀ c s₁ s₂ s₀ hs α β q
  have hright := extCoefficientTransfer_comp G₁ G₂ L₀ d t₁ t₂ s₀ ht γ δ q
  have hcoeff := congrArg (fun a : L₀.obj A ⟶ D => L₀.extCoefficientTransfer s₀ a q) hc
  exact DFunLike.congr_fun (hleft.trans (hcoeff.trans hright.symm)) x

/-- Evaluate an already-proved ordinary coefficient composite on the original Ext value. -/
theorem extPrecompMap_postcomp_of_comp_eq
    (L : C₀ ⥤ C₃) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {U : C₀} {V : C₃} (s : V ⟶ L.obj U)
    {A B : C₀} {C D : C₃} (a : A ⟶ B)
    (b : L.obj B ⟶ C) (c : C ⟶ D) (d : L.obj A ⟶ D)
    (h : L.map a ≫ b ≫ c = d) (n : ℕ) (x : Ext U A n) :
    ((L.extPrecompMap s B n (x.comp (Ext.mk₀ a) (add_zero n))).comp
        (Ext.mk₀ b) (add_zero n)).comp (Ext.mk₀ c) (add_zero n) =
      (L.extPrecompMap s A n x).comp (Ext.mk₀ d) (add_zero n) := by
  rw [Functor.extPrecompMap_comp, Ext.mapExactFunctor_mk₀]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Category.assoc]
  rw [h]

end CategoryTheory.Functor
