/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.Ext.SourceTransfer

/-! # Original exact Ext transfer on diagrams

The actual exact functor, natural source comparison and coefficient arrow
construct the full Ext-presheaf transformation before any geometric source
is substituted. The extension compatibility uses the same original transfer.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Functor

universe i j u v u' v' w w'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

section Diagram

variable [HasExt.{w} C] [HasExt.{w} D]
  {I : Type i} [Category.{j} I]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- The complete original Ext transfer on a diagram, with its naturality
proved before specializing the original diagrams or exact functor. The common
Ext value universe is the codomain of this natural transformation. -/
def extDiagramMap (F : I ⥤ C) (G : I ⥤ D) (e : F ⋙ L ≅ G)
    {A : C} {B : D} (a : L.obj A ⟶ B) (n : ℕ) :
    (F.op ⋙ extFunctor n).flip.obj A ⟶ (G.op ⋙ extFunctor n).flip.obj B where
  app U := AddCommGrpCat.ofHom (L.extCoefficientTransfer (e.inv.app U.unop) a n)
  naturality U V f := by
    ext x
    change Ext.{w} (F.obj U.unop) A n at x
    change ((Ext.mk₀ (e.inv.app V.unop)).comp
        (((Ext.mk₀ (F.map f.unop)).comp x (Nat.zero_add n)).mapExactFunctor L)
        (Nat.zero_add n)).comp (Ext.mk₀ a) (Nat.add_zero n) =
      (Ext.mk₀ (G.map f.unop)).comp
        (((Ext.mk₀ (e.inv.app U.unop)).comp (x.mapExactFunctor L) (Nat.zero_add n)).comp
          (Ext.mk₀ a) (Nat.add_zero n)) (Nat.zero_add n)
    simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      ← Ext.comp_assoc_of_third_deg_zero, ← Ext.comp_assoc_of_second_deg_zero,
      Ext.mk₀_comp_mk₀]
    exact congrArg (fun k => ((Ext.mk₀ k).comp (x.mapExactFunctor L)
      (Nat.zero_add n)).comp (Ext.mk₀ a) (Nat.add_zero n)) (e.inv.naturality f.unop).symm

end Diagram

section Extension

variable [HasExt.{w} C] [HasExt.{w'} D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- The original extension-class compatibility propagates through the complete
exact source/coefficient transfer. Source and target Ext universes are independent. -/
theorem extCoefficientTransfer_extension
    {U V A : C} {U' V' B : D} (sU : U' ⟶ L.obj U) (sV : V' ⟶ L.obj V)
    (a : L.obj A ⟶ B) (c : Ext.{w} U V 1) (d : Ext.{w'} U' V' 1)
    (hc : (Ext.mk₀ sU).comp (c.mapExactFunctor L) (Nat.zero_add 1) =
      d.comp (Ext.mk₀ sV) (Nat.add_zero 1))
    (n : ℕ) (x : Ext.{w} V A n) :
    L.extCoefficientTransfer sU a (n + 1)
        (c.comp x (show 1 + n = n + 1 by omega)) =
      d.comp (L.extCoefficientTransfer sV a n x) (show 1 + n = n + 1 by omega) := by
  change ((Ext.mk₀ sU).comp
      ((c.comp x (show 1 + n = n + 1 by omega)).mapExactFunctor L)
      (Nat.zero_add (n + 1))).comp (Ext.mk₀ a) (Nat.add_zero (n + 1)) =
    d.comp (((Ext.mk₀ sV).comp (x.mapExactFunctor L) (Nat.zero_add n)).comp
      (Ext.mk₀ a) (Nat.add_zero n)) (show 1 + n = n + 1 by omega)
  rw [Ext.mapExactFunctor_comp]
  rw [← Ext.comp_assoc _ _ _ (Nat.zero_add 1) (show 1 + n = n + 1 by omega)
    (show 0 + 1 + n = n + 1 by omega)]
  rw [hc]
  rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero]

end Extension

end CategoryTheory.Functor
