/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# Original Ext classes as bounded-below derived morphisms

The fully faithful bounded-below inclusion lifts the original Ext morphism
using its native shift comparison. Forgetting the bound recovers that same
morphism. The additive equivalence preserves Yoneda composition, degree-zero
morphisms and the original unsigned short-exact connecting arrow.

No enough-injectives, enough-projectives or exact-functor hypothesis is used.
The Ext and derived-category size universes remain independent. The protected
signed `Ext.δ` is not identified with an unsigned connecting map.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian

universe w w' v u

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasExt.{w} C] [HasDerivedCategory.{w'} C] {X Y Z : C}

omit [HasExt.{w} C] in
private theorem shiftedHom_map_ι_injective
    {K L : DerivedCategory.Plus C} {i : ℤ}
    {f g : ShiftedHom K L i}
    (h : f.map DerivedCategory.Plus.ι = g.map DerivedCategory.Plus.ι) : f = g := by
  apply DerivedCategory.Plus.ι.map_injective
  exact (cancel_mono ((DerivedCategory.Plus.ι.commShiftIso i).hom.app L)).mp h

/-- Lift the original Ext morphism through the native bounded-below inclusion. -/
def homPlus {n : ℕ} (x : Ext.{w} X Y n) :
    ShiftedHom ((DerivedCategory.Plus.singleFunctor C 0).obj X)
      ((DerivedCategory.Plus.singleFunctor C 0).obj Y) (n : ℤ) :=
  DerivedCategory.Plus.ι.preimage
    (x.hom ≫ (DerivedCategory.Plus.ι.commShiftIso (n : ℤ)).inv.app
      ((DerivedCategory.Plus.singleFunctor C 0).obj Y))

/-- Forgetting the lower bound recovers the original shifted Ext morphism. -/
@[simp]
theorem homPlus_map {n : ℕ} (x : Ext.{w} X Y n) :
    x.homPlus.map DerivedCategory.Plus.ι = x.hom := by
  dsimp only [homPlus, ShiftedHom.map]
  rw [Functor.map_preimage, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id x.hom

/-- The bounded-below lift distinguishes every original Ext class. -/
theorem homPlus_injective (n : ℕ) :
    Function.Injective (homPlus (X := X) (Y := Y) (n := n)) := by
  intro x y h
  apply Ext.ext
  simpa only [homPlus_map] using congrArg (fun f => f.map DerivedCategory.Plus.ι) h

/-- Original Ext is additively equivalent to shifted Hom between native D+ singles. -/
def homPlusAddEquiv (n : ℕ) :
    Ext.{w} X Y n ≃+
      ShiftedHom ((DerivedCategory.Plus.singleFunctor C 0).obj X)
        ((DerivedCategory.Plus.singleFunctor C 0).obj Y) (n : ℤ) where
  toFun := homPlus
  invFun f := homEquiv.symm (f.map DerivedCategory.Plus.ι)
  left_inv x := by
    apply Ext.ext
    change homEquiv (homEquiv.symm (x.homPlus.map DerivedCategory.Plus.ι)) = x.hom
    rw [Equiv.apply_symm_apply]
    exact homPlus_map x
  right_inv f := by
    apply shiftedHom_map_ι_injective
    rw [homPlus_map]
    exact homEquiv.apply_symm_apply _
  map_add' x y := by
    apply shiftedHom_map_ι_injective
    rw [homPlus_map, ShiftedHom.map_add, homPlus_map, homPlus_map, add_hom]

/-- The additive equivalence has the original fully faithful lift as its forward map. -/
@[simp]
theorem homPlusAddEquiv_apply (n : ℕ) (x : Ext.{w} X Y n) :
    homPlusAddEquiv n x = x.homPlus := rfl

/-- An original degree-zero morphism gives the native shifted-Hom degree-zero class. -/
@[simp]
theorem homPlus_mk₀ (f : X ⟶ Y) :
    (mk₀ f).homPlus = ShiftedHom.mk₀ (0 : ℤ) rfl
      ((DerivedCategory.Plus.singleFunctor C 0).map f) := by
  apply shiftedHom_map_ι_injective
  rw [homPlus_map, mk₀_hom]
  exact (ShiftedHom.map_mk₀ (0 : ℤ) rfl
    ((DerivedCategory.Plus.singleFunctor C 0).map f) DerivedCategory.Plus.ι).symm

/-- The native bounded-below lift preserves the original Yoneda composition. -/
theorem homPlus_comp {a b c : ℕ} (x : Ext.{w} X Y a) (y : Ext.{w} Y Z b)
    (h : a + b = c) :
    (x.comp y h).homPlus = x.homPlus.comp y.homPlus (by omega) := by
  apply shiftedHom_map_ι_injective
  rw [homPlus_map, ShiftedHom.map_comp, homPlus_map, homPlus_map, comp_hom]

/-- The original extension class lifts to the actual unsigned D+ connecting arrow. -/
theorem homPlus_extClass {S : ShortComplex C} (hS : S.ShortExact) :
    hS.extClass.homPlus = hS.singleTrianglePlus.mor₃ := by
  dsimp only [homPlus, ShortComplex.ShortExact.singleTrianglePlus]
  rw [ShortComplex.ShortExact.extClass_hom]
  rfl

end CategoryTheory.Abelian.Ext
