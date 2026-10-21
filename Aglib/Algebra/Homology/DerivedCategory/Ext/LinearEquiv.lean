/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Linear transport and finite biproducts for Ext

The native scalar-compatible composition defines linear equivalences from
actual isomorphisms in either variable. Native finite-biproduct additivity is
upgraded to an R-linear equivalence with its original inclusions and projections.
The category, scalar ring, and Ext universes are independent.
-/

@[expose] public section

noncomputable section

universe t w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

variable (R : Type t) [CommRing R] {C : Type u} [Category.{v} C] [Abelian C]
    [Linear R C] [HasExt.{w} C]

/-- Precomposition with the original isomorphism induces a linear equivalence
in the first, contravariant Ext variable. -/
def precompLinearEquiv {X Y : C} (e : X ≅ Y) (Z : C) (n : ℕ) :
    Ext.{w} Y Z n ≃ₗ[R] Ext.{w} X Z n :=
  { (mk₀ e.hom).precompOfLinear R Z (zero_add n) with
    invFun := fun x => (mk₀ e.inv).comp x (zero_add n)
    left_inv := fun x => by
      change (mk₀ e.inv).comp ((mk₀ e.hom).comp x (zero_add n)) (zero_add n) = x
      simp only [← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀,
        e.inv_hom_id, mk₀_id_comp]
    right_inv := fun x => by
      change (mk₀ e.hom).comp ((mk₀ e.inv).comp x (zero_add n)) (zero_add n) = x
      simp only [← comp_assoc_of_second_deg_zero, mk₀_comp_mk₀,
        e.hom_inv_id, mk₀_id_comp] }

/-- Postcomposition with the original isomorphism induces a linear equivalence
in the second, covariant Ext variable. -/
def postcompLinearEquiv {X Y : C} (e : X ≅ Y) (Z : C) (n : ℕ) :
    Ext.{w} Z X n ≃ₗ[R] Ext.{w} Z Y n :=
  { (mk₀ e.hom).postcompOfLinear R Z (add_zero n) with
    invFun := fun x => x.comp (mk₀ e.inv) (add_zero n)
    left_inv := fun x => by
      change (x.comp (mk₀ e.hom) (add_zero n)).comp (mk₀ e.inv) (add_zero n) = x
      simp only [comp_assoc_of_second_deg_zero, mk₀_comp_mk₀,
        e.hom_inv_id, comp_mk₀_id]
    right_inv := fun x => by
      change (x.comp (mk₀ e.inv) (add_zero n)).comp (mk₀ e.hom) (add_zero n) = x
      simp only [comp_assoc_of_second_deg_zero, mk₀_comp_mk₀,
        e.inv_hom_id, comp_mk₀_id] }

/-- Finite-biproduct additivity in the first variable respects the actual
R-module structure on Ext. -/
def biproductLinearEquiv {J : Type*} [Fintype J] {X : J → C} {c : Bicone X}
    (hc : c.IsBilimit) (Y : C) (n : ℕ) :
    Ext.{w} c.pt Y n ≃ₗ[R] ∀ j, Ext.{w} (X j) Y n :=
  { biproductAddEquiv hc Y n with
    map_smul' := fun r x => by
      ext j
      exact comp_smul (mk₀ (c.ι j)) x (zero_add n) r }

/-- The first-variable transport retains the original degree-zero morphism. -/
@[simp]
theorem precompLinearEquiv_apply {X Y : C} (e : X ≅ Y) (Z : C) (n : ℕ)
    (x : Ext.{w} Y Z n) :
    precompLinearEquiv R e Z n x = (mk₀ e.hom).comp x (zero_add n) := rfl

/-- The second-variable transport retains the original degree-zero morphism. -/
@[simp]
theorem postcompLinearEquiv_apply {X Y : C} (e : X ≅ Y) (Z : C) (n : ℕ)
    (x : Ext.{w} Z X n) :
    postcompLinearEquiv R e Z n x = x.comp (mk₀ e.hom) (add_zero n) := rfl

/-- A biproduct component is precomposition with the original inclusion. -/
@[simp]
theorem biproductLinearEquiv_apply {J : Type*} [Fintype J] {X : J → C}
    {c : Bicone X} (hc : c.IsBilimit) (Y : C) (n : ℕ)
    (x : Ext.{w} c.pt Y n) (j : J) :
    biproductLinearEquiv R hc Y n x j = (mk₀ (c.ι j)).comp x (zero_add n) := rfl

end CategoryTheory.Abelian.Ext
