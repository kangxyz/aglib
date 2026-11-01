/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Universe change for the original Ext operations

The native universe equivalence preserves composition, zero, and exact-functor
maps. One derived realization per category proves these equations; no alternate
cohomology group or comparison map is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

universe u v u' v' e₀ e₁ d₀ d₁

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasExt.{e₀} C] [HasExt.{e₁} C]

/-- Native universe change preserves zero. -/
@[simp]
theorem chgUniv_zero {X Y : C} {n : ℕ} :
    chgUniv.{e₁} (0 : Ext.{e₀} X Y n) = 0 := by
  let := HasDerivedCategory.standard C
  apply homEquiv.injective
  change (chgUniv.{e₁} (0 : Ext.{e₀} X Y n)).hom = (0 : Ext.{e₁} X Y n).hom
  simp only [homEquiv_chgUniv, zero_hom]

/-- Native universe change preserves degree-zero morphisms. -/
@[simp]
theorem chgUniv_mk₀ {X Y : C} (f : X ⟶ Y) :
    chgUniv.{e₁} (mk₀ f : Ext.{e₀} X Y 0) = mk₀ f := by
  let := HasDerivedCategory.standard C
  apply homEquiv.injective
  change (chgUniv.{e₁} (mk₀ f : Ext.{e₀} X Y 0)).hom = (mk₀ f : Ext.{e₁} X Y 0).hom
  simp only [homEquiv_chgUniv, mk₀_hom]

/-- Native universe change preserves the original Yoneda composition. -/
theorem chgUniv_comp {X Y Z : C} {a b c : ℕ}
    (x : Ext.{e₀} X Y a) (y : Ext.{e₀} Y Z b) (h : a + b = c) :
    chgUniv.{e₁} (x.comp y h) =
      (chgUniv.{e₁} x).comp (chgUniv.{e₁} y) h := by
  let := HasDerivedCategory.standard C
  apply homEquiv.injective
  change (chgUniv.{e₁} (x.comp y h)).hom =
    ((chgUniv.{e₁} x).comp (chgUniv.{e₁} y) h).hom
  simp only [homEquiv_chgUniv, comp_hom]

variable {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{d₀} D] [HasExt.{d₁} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The original exact-functor map commutes with independent source and target
universe changes. -/
theorem chgUniv_mapExactFunctor {X Y : C} {n : ℕ} (x : Ext.{e₀} X Y n) :
    chgUniv.{d₁} (x.mapExactFunctor.{e₀, d₀} F : Ext.{d₀} (F.obj X) (F.obj Y) n) =
      ((chgUniv.{e₁} x).mapExactFunctor.{e₁, d₁} F : Ext.{d₁} (F.obj X) (F.obj Y) n) := by
  let := HasDerivedCategory.standard C
  let := HasDerivedCategory.standard D
  apply homEquiv.injective
  change (chgUniv.{d₁} (x.mapExactFunctor.{e₀, d₀} F :
    Ext.{d₀} (F.obj X) (F.obj Y) n)).hom =
      ((chgUniv.{e₁} x).mapExactFunctor.{e₁, d₁} F : Ext.{d₁} (F.obj X) (F.obj Y) n).hom
  simp only [homEquiv_chgUniv, mapExactFunctor_hom]

end CategoryTheory.Abelian.Ext
