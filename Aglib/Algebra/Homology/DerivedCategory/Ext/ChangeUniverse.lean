/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Linearity of the original Ext universe comparison

The native `Ext.chgUniv` preserves the unchanged scalar action. This upgrades
that same equivalence, rather than choosing another Ext comparison. The current
consumer transports native finite-generation results to a specified Ext size
before applying the original source-algebra action on higher coinduction.
-/

@[expose] public section
noncomputable section

universe t u v w w'

namespace CategoryTheory.Abelian.Ext

variable (R : Type t) [Ring R] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear R C] [HasExt.{w} C] [HasExt.{w'} C]

/-- The native change of Ext universe is linear for the original scalar action. -/
def chgUnivLinearEquiv (X Y : C) (n : ℕ) :
    Ext.{w} X Y n ≃ₗ[R] Ext.{w'} X Y n := by
  let := HasDerivedCategory.standard C
  refine { (chgUniv.{w', w} : Ext.{w} X Y n ≃ Ext.{w'} X Y n) with
    map_add' := ?_
    map_smul' := ?_ }
  · intro x y
    apply (homEquiv : Ext.{w'} X Y n ≃ _).injective
    simp only [Equiv.toFun_as_coe, homEquiv_chgUniv.{max u v, w', w}, add_hom]
  · intro r x
    apply (homEquiv : Ext.{w'} X Y n ≃ _).injective
    simp only [Equiv.toFun_as_coe, homEquiv_chgUniv.{max u v, w', w}, smul_hom,
      RingHom.id_apply]

/-- The linear upgrade retains the native universe-change map literally. -/
@[simp]
theorem chgUnivLinearEquiv_toEquiv (X Y : C) (n : ℕ) :
    (chgUnivLinearEquiv.{t, u, v, w, w'} R X Y n).toEquiv =
      (chgUniv.{w', w} : Ext.{w} X Y n ≃ Ext.{w'} X Y n) := rfl

end CategoryTheory.Abelian.Ext
