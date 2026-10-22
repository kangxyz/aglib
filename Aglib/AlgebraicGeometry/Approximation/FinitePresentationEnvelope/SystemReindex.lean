/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.System

/-!
# Initial reindexing of actual arithmetic approximation systems

The original scheme and its projections are retained literally. The stages
and transitions are those of the original diagram along the supplied initial
functor, and the limiting property is transported by native initiality.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope.System

variable {X : Scheme.{u}} (M : System X)
  {J : Type u} [Category.{u} J] [IsCofiltered J]
  (F : J ⥤ M.Index) [F.Initial]

/-- Restrict an actual arithmetic system along an initial functor without
changing its original source or replacing any stages or transition maps. -/
def reindex : System X where
  Index := J
  category := inferInstance
  cofiltered := inferInstance
  diagram := F ⋙ M.diagram
  projection := (M.cone.whisker F).π
  isLimit := (Functor.Initial.isLimitWhiskerEquiv F M.cone).symm M.isLimit
  affine r := M.affine (F.map r)
  finiteType j := M.finiteType (F.obj j)
  compact j := M.compact (F.obj j)

@[simp]
lemma reindex_diagram_obj (j : J) :
    (M.reindex F).diagram.obj j = M.diagram.obj (F.obj j) := rfl

@[simp]
lemma reindex_diagram_map {i j : J} (r : i ⟶ j) :
    (M.reindex F).diagram.map r = M.diagram.map (F.map r) := rfl

@[simp]
lemma reindex_projection_app (j : J) :
    (M.reindex F).projection.app j = M.projection.app (F.obj j) := rfl

/-- The cone is the literal whiskered original cone, not an isomorphic model. -/
lemma reindex_cone : (M.reindex F).cone = M.cone.whisker F := rfl

end AlgebraicGeometry.Scheme.FinitePresentationEnvelope.System
