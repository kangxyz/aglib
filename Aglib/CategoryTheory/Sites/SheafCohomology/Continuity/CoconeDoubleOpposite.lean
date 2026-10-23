/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Opposites

/-! # Remove a double-opposite index from an actual mapped cocone -/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace CategoryTheory.Limits

/-- A mapped cocone is colimiting if its native left-opposite cone form is colimiting. -/
def isColimitMapCoconeOfLeftOp {J C E : Type*}
    [Category J] [Category C] [Category E]
    (D : J ⥤ Cᵒᵖ) (c : Cocone D) (P : Cᵒᵖ ⥤ E)
    (h : IsColimit (P.mapCocone (coneLeftOpOfCocone c).op)) :
    IsColimit (P.mapCocone c) :=
  (Functor.Final.isColimitWhiskerEquiv (opOp J)
    (P.mapCocone (coneLeftOpOfCocone c).op)).symm h

end CategoryTheory.Limits
