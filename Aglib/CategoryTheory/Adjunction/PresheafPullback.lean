/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Opposites

/-! # Presheaf pullback through an original adjunction

Restriction along the counit and a specified coefficient arrow are assembled
before specializing the categories. This retains the original counit and all
presheaf transition maps, without comparing concrete opposite composites.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.Adjunction

universe u v u' v' w w'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type w} [Category.{w'} E] {L : C ⥤ D} {R : D ⥤ C}
  (adj : L ⊣ R) (P : Dᵒᵖ ⥤ E) (Q : Cᵒᵖ ⥤ E)
  (α : L.op ⋙ P ⟶ Q)

/-- Restrict along the actual counit and then apply the actual coefficient arrow. -/
def presheafPullbackUnit : P ⟶ R.op ⋙ Q where
  app U := P.map (adj.counit.app U.unop).op ≫ α.app (op (R.obj U.unop))
  naturality {U V} g := by
    have h := congrArg (fun k => P.map k.op) (adj.counit.naturality g.unop)
    simp only [op_comp, Functor.map_comp, Functor.id_map, Functor.comp_map,
      Quiver.Hom.op_unop] at h
    dsimp only [Functor.comp_map, Functor.op_map]
    rw [← Category.assoc, ← h, Category.assoc, Category.assoc]
    exact congrArg (fun k => P.map (adj.counit.app U.unop).op ≫ k)
      (α.naturality ((R.map g.unop).op))

/-- Each component keeps precisely the original counit restriction. -/
@[simp]
theorem presheafPullbackUnit_app (U : Dᵒᵖ) :
    (presheafPullbackUnit adj P Q α).app U =
      P.map (adj.counit.app U.unop).op ≫ α.app (op (R.obj U.unop)) := rfl

end CategoryTheory.Adjunction
