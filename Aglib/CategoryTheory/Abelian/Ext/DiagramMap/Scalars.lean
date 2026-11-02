/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Preadditive.ScalarDiagram
public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap

/-! # Original Ext diagrams with a coefficient-ring action

The unchanged Ext groups and original index maps are the additive coefficient
functor supplied to the complete scalar-diagram construction. One specified
`HasExt` world and the original coefficient endomorphisms are used throughout.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite

universe u v i j w r

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {I : Type i} [Category.{j} I] (F : I ⥤ C)

instance extCoefficientDiagram_additive (n : ℕ) :
    ((F.op ⋙ extFunctor.{w} n).flip).Additive where
  map_add {A B} {f g} := by
    ext U x
    change Ext.{w} (F.obj U.unop) A n at x
    change x.comp (Ext.mk₀ (f + g)) (Nat.add_zero n) =
      x.comp (Ext.mk₀ f) (Nat.add_zero n) + x.comp (Ext.mk₀ g) (Nat.add_zero n)
    rw [Ext.mk₀_add, Ext.comp_add]

variable {R : Type r} [Ring R] (A : C) (ρ : R →+* End A) (n : ℕ)

/-- The specified coefficient action on the original Ext group at each index. -/
abbrev extCoefficientModule (U : Iᵒᵖ) : Module R (Ext.{w} (F.obj U.unop) A n) :=
  ((F.op ⋙ extFunctor.{w} n).flip).coefficientModule A ρ U

/-- The whole original Ext diagram with its original coefficient scalar action. -/
def extModuleDiagram : Iᵒᵖ ⥤ ModuleCat.{w} R :=
  ((F.op ⋙ extFunctor.{w} n).flip).coefficientModuleDiagram A ρ

/-- Forgetting scalars retains the exact original Ext functor, not an isomorphic model. -/
def extModuleDiagramForgetIso :
    F.extModuleDiagram A ρ n ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w} ≅
      (F.op ⋙ extFunctor.{w} n).flip.obj A :=
  ((F.op ⋙ extFunctor.{w} n).flip).coefficientModuleDiagramForgetIso A ρ

/-- The original coefficient action is literal postcomposition by its degree-zero Ext class. -/
theorem extModuleDiagram_smul (U : Iᵒᵖ) (a : R) (x : Ext.{w} (F.obj U.unop) A n) :
    letI := F.extCoefficientModule A ρ n U
    a • x = x.comp (Ext.mk₀ (ρ a)) (Nat.add_zero n) := rfl

/-- The enriched index map is the original degree-zero source precomposition. -/
theorem extModuleDiagram_map_apply {U V : Iᵒᵖ} (f : U ⟶ V)
    (x : Ext.{w} (F.obj U.unop) A n) :
    (F.extModuleDiagram A ρ n).map f x =
      (Ext.mk₀ (F.map f.unop)).comp x (Nat.zero_add n) := rfl

end CategoryTheory.Functor
