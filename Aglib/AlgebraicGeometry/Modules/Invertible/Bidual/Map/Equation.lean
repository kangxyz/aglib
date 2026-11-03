/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.Map

/-! # Equation -/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable (X : Scheme.{u})
  {M N : SheafOfModules.{u} X.ringCatSheaf}

/-- The original extension is its original double-dual map followed by line biduality. -/
theorem extendToBidualLine_eq (L : LineBundle X) (h : M ⟶ L.val) :
    extendToBidualLine X L h = doubleDualMap X h ≫ (bidualIso X L).inv := by
  rfl

end AlgebraicGeometry.Scheme.Modules.Invertible
