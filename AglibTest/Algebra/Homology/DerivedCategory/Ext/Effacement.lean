/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.Effacement

/-! The original Ext world suffices; there is no projective/injective-supply input. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe u v w

example {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {X Y : C} {n : ℕ} (x : Ext.{w} X Y (n + 1)) :
    ∃ (M : C) (f : M ⟶ X), Epi f ∧ (Ext.mk₀ f).comp x (zero_add (n + 1)) = 0 :=
  Ext.exists_epi_mk₀_comp_eq_zero x

end

/--
info: 'CategoryTheory.Abelian.Ext.exists_epi_mk₀_comp_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.Abelian.Ext.exists_epi_mk₀_comp_eq_zero
