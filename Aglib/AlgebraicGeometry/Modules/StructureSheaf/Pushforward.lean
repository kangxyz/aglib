/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Direct image of the structure module sheaf

The actual scalar-restricted module sheaf `f_* O_X` for an arbitrary scheme
morphism, extracted from `R5Lab.AlgebraicGeometry.Curves.Degree.Basic:40–42`
at revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X Y : Scheme.{u}}

/-- The actual module sheaf `f_* O_X`, with scalar restriction along `f`. -/
def pushforwardStructureSheaf (f : X ⟶ Y) : SheafOfModules Y.ringCatSheaf :=
  (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)

end AlgebraicGeometry.Scheme.Modules
