/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-! An original signed extension detects its original character. -/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian

namespace CategoryTheory.Abelian.Ext

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Equality of the two signed values detects the original character through
the given character equivalence and injective class map. -/
theorem eq_character_of_signed_postcomp {Y : Type*} {U K M : C}
    (c : Ext.{w} U K 1) (e : Y ≃ (K ⟶ M)) (q : Y → Ext.{w} U M 1)
    (hq : Function.Injective q)
    (h : ∀ y, c.comp (Ext.mk₀ (e y)) (add_zero 1) = -q y)
    (y : Y) (f : K ⟶ M)
    (hf : c.comp (Ext.mk₀ f) (add_zero 1) = -q y) : f = e y := by
  let y' := e.symm f
  have he : e y' = f := e.apply_symm_apply f
  have h' : -q y' = -q y := (h y').symm.trans
    ((congrArg (fun a => c.comp (Ext.mk₀ a) (add_zero 1)) he).trans hf)
  exact he.symm.trans (congrArg e (hq (neg_injective h')))

end CategoryTheory.Abelian.Ext
