/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.PresheafPullback

/-! # The original presheaf pullback unit on arbitrary transition arrows

Normalize the whole counit/coefficient/transition composite before supplying
concrete section coefficients. The result keeps the original adjunct arrow.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.Adjunction

universe u v u' v' w w'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type w} [Category.{w'} E] {L : C ⥤ D} {R : D ⥤ C}
  (adj : L ⊣ R) (P : Dᵒᵖ ⥤ E) (Q : Cᵒᵖ ⥤ E)
  (α : L.op ⋙ P ⟶ Q)

/-- Restriction after the actual unit is restriction along the original adjunct,
followed by the same coefficient arrow. -/
theorem presheafPullbackUnit_app_comp {U : D} {V : C} (g : V ⟶ R.obj U) :
    (presheafPullbackUnit adj P Q α).app (op U) ≫ Q.map g.op =
      P.map (L.map g ≫ adj.counit.app U).op ≫ α.app (op V) := by
  rw [presheafPullbackUnit_app, Category.assoc, ← α.naturality g.op]
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
    op_comp, Functor.map_comp, Category.assoc]

end CategoryTheory.Adjunction
