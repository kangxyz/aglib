/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Original constant-sheaf transposition and coefficient composition

The actual constant/compose comparison and its original counit equation give
the whole transpose formula. No preservation of injectives, derived category
or alternative constant or section carrier is involved.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.OriginalSections

universe uC vC uA vA uB vB

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  [HasWeakSheafify J A] [HasWeakSheafify J B]
  (U : A ⥤ B) [J.PreservesSheafification U] [J.HasSheafCompose U]
  {T : C} (hT : IsTerminal T)

/-- The original constant-adjunction transpose commutes with actual coefficient composition. -/
theorem constantAdjoint_compose (M : A) (F : Sheaf J A) (a : M ⟶ F.obj.obj (op T)) :
    (constantCommuteCompose J U).inv.app M ≫
        (sheafCompose J U).map (((constantSheafAdj J A hT).homEquiv M F).symm a) =
      ((constantSheafAdj J B hT).homEquiv (U.obj M) ((sheafCompose J U).obj F)).symm
        (U.map a) := by
  rw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_symm_apply, Functor.map_comp]
  have hn : (U ⋙ constantSheaf J B).map a ≫ (constantCommuteCompose J U).inv.app _ =
      (constantCommuteCompose J U).inv.app M ≫
        (sheafCompose J U).map ((constantSheaf J A).map a) :=
    (constantCommuteCompose J U).inv.naturality a
  rw [← Category.assoc, ← hn]
  rw [Category.assoc, ← constantSheafAdj_counit_w J U F hT,
    ← Category.assoc ((constantCommuteCompose J U).inv.app (F.obj.obj (op T))),
    Iso.inv_hom_id_app, Category.id_comp]
  rw [Functor.comp_map]

end CategoryTheory.Sheaf.OriginalSections
