/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Grp.Basic

/-! # Constant-sheaf adjunction values at the actual terminal objects

The evaluation is the original sheafification unit followed by the given sheaf
map. Its terminal restriction law uses naturality of that same composite.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.ConstantTerminalValues

universe u v w

variable {C : Type u} [Category.{v} C]
  (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]

/-- The original adjunction evaluates the actual sheafification-unit composite. -/
theorem homEquiv_app {T : C} (hT : IsTerminal T) (A : AddCommGrpCat.{w})
    (F : Sheaf J AddCommGrpCat.{w}) (a : (constantSheaf J AddCommGrpCat.{w}).obj A ⟶ F) :
    (constantSheafAdj J AddCommGrpCat.{w} hT).homEquiv A F a =
      (toSheafify J ((Functor.const Cᵒᵖ).obj A) ≫ a.hom).app (op T) := by
  ext x
  rfl

/-- Restriction between the actual terminal tests preserves this same value. -/
theorem homEquiv_restrict {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T')
    (g : T' ⟶ T) (A : AddCommGrpCat.{w}) (F : Sheaf J AddCommGrpCat.{w})
    (a : (constantSheaf J AddCommGrpCat.{w}).obj A ⟶ F) :
    (constantSheafAdj J AddCommGrpCat.{w} hT).homEquiv A F a ≫ F.obj.map g.op =
      (constantSheafAdj J AddCommGrpCat.{w} hT').homEquiv A F a := by
  rw [homEquiv_app, homEquiv_app]
  exact ((toSheafify J ((Functor.const Cᵒᵖ).obj A) ≫ a.hom).naturality g.op).symm.trans
    (Category.id_comp _)

end CategoryTheory.Sheaf.ConstantTerminalValues
