/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.CompositeComparison

/-! # Exact Ext transfer through the original source and coefficient maps

The complete transfer uses one exact functor and the actual two arrows.
Identity and composition retain their original whole comparisons and ordinary
source equations, with independent category, Hom and Ext universes.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Functor

universe u₀ v₀ u₁ v₁ u₂ v₂ e₀ e₁ e₂

variable {C₀ : Type u₀} [Category.{v₀} C₀] [Abelian C₀] [HasExt.{e₀} C₀]
  {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasExt.{e₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasExt.{e₂} C₂]

/-- Exact image followed by the actual inverse source and coefficient arrows,
with independent source and target Ext worlds. -/
def extCoefficientTransfer (L : C₀ ⥤ C₁) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {U : C₀} {V : C₁} (s : V ⟶ L.obj U)
    {F : C₀} {G : C₁} (φ : L.obj F ⟶ G) (n : ℕ) :
    Ext.{e₀} U F n →+ Ext.{e₁} V G n :=
  ((Ext.mk₀ φ).postcomp V (add_zero n)).comp (L.extPrecompMap s F n)

theorem extCoefficientTransfer_apply (L : C₀ ⥤ C₁) [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {U : C₀} {V : C₁} (s : V ⟶ L.obj U)
    {F : C₀} {G : C₁} (φ : L.obj F ⟶ G) (n : ℕ) (x : Ext.{e₀} U F n) :
    L.extCoefficientTransfer s φ n x =
      (L.extPrecompMap s F n x).comp (Ext.mk₀ φ) (add_zero n) := rfl

/-- Whole exact-functor comparison with its original source-arrow equation. -/
theorem extPrecompMap_comparison
    (L₁ : C₀ ⥤ C₁) [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    (L₂ : C₁ ⥤ C₂) [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    (L₀ : C₀ ⥤ C₂) [L₀.Additive] [PreservesFiniteLimits L₀] [PreservesFiniteColimits L₀]
    (c : L₀ ≅ L₁ ⋙ L₂) {U₀ : C₀} {U₁ : C₁} {U₂ : C₂}
    (s₁ : U₁ ⟶ L₁.obj U₀) (s₂ : U₂ ⟶ L₂.obj U₁) (s₀ : U₂ ⟶ L₀.obj U₀)
    (hs : s₀ ≫ c.hom.app U₀ = s₂ ≫ L₂.map s₁)
    (F : C₀) (n : ℕ) (x : Ext.{e₀} U₀ F n) :
    (L₀.extPrecompMap s₀ F n x).comp (Ext.mk₀ (c.hom.app F)) (add_zero n) =
      L₂.extPrecompMap s₂ (L₁.obj F) n (L₁.extPrecompMap s₁ F n x) := by
  rw [Functor.extPrecompMap_apply, Ext.comp_assoc_of_third_deg_zero,
    Ext.mapExactFunctor_comp_mk₀_natTransApp, Ext.mk₀_comp_mk₀_assoc, hs]
  exact L₁.extPrecompMap_compFunctor L₂ s₁ s₂ F n x

/-- The complete transfer composes through the actual whole comparison and
ordinary source coherence, before any diagram or cocone is chosen. -/
theorem extCoefficientTransfer_comp
    (L₁ : C₀ ⥤ C₁) [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    (L₂ : C₁ ⥤ C₂) [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    (L₀ : C₀ ⥤ C₂) [L₀.Additive] [PreservesFiniteLimits L₀] [PreservesFiniteColimits L₀]
    (c : L₀ ≅ L₁ ⋙ L₂) {U₀ : C₀} {U₁ : C₁} {U₂ : C₂}
    (s₁ : U₁ ⟶ L₁.obj U₀) (s₂ : U₂ ⟶ L₂.obj U₁) (s₀ : U₂ ⟶ L₀.obj U₀)
    (hs : s₀ ≫ c.hom.app U₀ = s₂ ≫ L₂.map s₁)
    {F : C₀} {G : C₁} {H : C₂} (φ : L₁.obj F ⟶ G) (ψ : L₂.obj G ⟶ H) (n : ℕ) :
    (L₂.extCoefficientTransfer s₂ ψ n).comp (L₁.extCoefficientTransfer s₁ φ n) =
      L₀.extCoefficientTransfer s₀ (c.hom.app F ≫ L₂.map φ ≫ ψ) n := by
  ext x
  have hp := extPrecompMap_comparison L₁ L₂ L₀ c s₁ s₂ s₀ hs F n x
  change (L₂.extPrecompMap s₂ G n
      ((L₁.extPrecompMap s₁ F n x).comp (Ext.mk₀ φ) (add_zero n))).comp
        (Ext.mk₀ ψ) (add_zero n) = _
  rw [Functor.extPrecompMap_comp, Ext.mapExactFunctor_mk₀, ← hp]
  simp only [extCoefficientTransfer_apply, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, Category.assoc]

/-- Normalize the complete composite to the supplied actual coefficient arrow. -/
theorem extCoefficientTransfer_comp_of_eq
    (L₁ : C₀ ⥤ C₁) [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    (L₂ : C₁ ⥤ C₂) [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    (L₀ : C₀ ⥤ C₂) [L₀.Additive] [PreservesFiniteLimits L₀] [PreservesFiniteColimits L₀]
    (c : L₀ ≅ L₁ ⋙ L₂) {U₀ : C₀} {U₁ : C₁} {U₂ : C₂}
    (s₁ : U₁ ⟶ L₁.obj U₀) (s₂ : U₂ ⟶ L₂.obj U₁) (s₀ : U₂ ⟶ L₀.obj U₀)
    (hs : s₀ ≫ c.hom.app U₀ = s₂ ≫ L₂.map s₁)
    {F : C₀} {G : C₁} {H : C₂}
    (φ : L₁.obj F ⟶ G) (ψ : L₂.obj G ⟶ H) (χ : L₀.obj F ⟶ H)
    (hχ : c.hom.app F ≫ L₂.map φ ≫ ψ = χ) (n : ℕ) :
    (L₂.extCoefficientTransfer s₂ ψ n).comp (L₁.extCoefficientTransfer s₁ φ n) =
      L₀.extCoefficientTransfer s₀ χ n := by
  exact (extCoefficientTransfer_comp L₁ L₂ L₀ c s₁ s₂ s₀ hs φ ψ n).trans
    (congrArg (fun k => L₀.extCoefficientTransfer s₀ k n) hχ)

/-- Source and coefficient units give the identity of the original Ext group. -/
theorem extCoefficientTransfer_id
    (L : C₀ ⥤ C₀) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (c : L ≅ 𝟭 C₀) {U : C₀} (s : U ⟶ L.obj U)
    (hs : s ≫ c.hom.app U = 𝟙 U) (F : C₀) (n : ℕ) :
    L.extCoefficientTransfer s (c.hom.app F) n = AddMonoidHom.id (Ext.{e₀} U F n) := by
  ext x
  change (L.extPrecompMap s F n x).comp (Ext.mk₀ (c.hom.app F)) (add_zero n) = x
  rw [Functor.extPrecompMap_apply, Ext.comp_assoc_of_third_deg_zero,
    Ext.mapExactFunctor_comp_mk₀_natTransApp, Ext.id_mapExactFunctor,
    Ext.mk₀_comp_mk₀_assoc, hs]
  simp

/-- The actual coefficient square gives the complete transfer naturality law. -/
theorem extCoefficientTransfer_naturality
    (L : C₀ ⥤ C₁) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {U : C₀} {V : C₁} (s : V ⟶ L.obj U)
    {F F' : C₀} {G G' : C₁} (φ : L.obj F ⟶ G) (ψ : L.obj F' ⟶ G')
    (a : F ⟶ F') (b : G ⟶ G') (h : L.map a ≫ ψ = φ ≫ b) (n : ℕ) :
    ((Ext.mk₀ b).postcomp V (add_zero n)).comp (L.extCoefficientTransfer s φ n) =
      (L.extCoefficientTransfer s ψ n).comp ((Ext.mk₀ a).postcomp U (add_zero n)) := by
  ext x
  change ((L.extPrecompMap s F n x).comp (Ext.mk₀ φ) (add_zero n)).comp
      (Ext.mk₀ b) (add_zero n) =
    (L.extPrecompMap s F' n (x.comp (Ext.mk₀ a) (add_zero n))).comp
      (Ext.mk₀ ψ) (add_zero n)
  rw [Functor.extPrecompMap_comp, Ext.mapExactFunctor_mk₀]
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  rw [h]

end CategoryTheory.Functor
