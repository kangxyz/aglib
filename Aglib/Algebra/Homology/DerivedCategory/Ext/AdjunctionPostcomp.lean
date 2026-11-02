/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.AdjunctionAcyclic

/-! # The original Ext counit map through an arbitrary coefficient adjunct -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Adjunction

universe u v u' v' e e'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{e} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{e'} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (adj : L ⊣ R)

/-- Postcomposition before the original counit Ext comparison is postcomposition
with the actual adjoint after the unchanged exact-functor Ext map. -/
theorem extCounitMap_postcomp {A A' : C} {B : D}
    (h : A' ⟶ R.obj B) (n : ℕ) (x : Ext.{e} A A' n) :
    adj.extCounitMap A B n (x.comp (Ext.mk₀ h) (Nat.add_zero n)) =
      (x.mapExactFunctor L).comp
        (Ext.mk₀ (((adj.homEquiv A' B).symm) h)) (Nat.add_zero n) := by
  simp only [extCounitMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Adjunction.homEquiv_counit]
  rw [Ext.comp_assoc _ _ _ _ (Nat.add_zero 0) (by omega), Ext.mk₀_comp_mk₀]

end CategoryTheory.Adjunction
