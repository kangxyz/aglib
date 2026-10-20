/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Charts
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Reindex
public import Aglib.AlgebraicGeometry.SchemeOverField

/-! The original polynomial P¹ and its native lifted-coordinate comparison. -/




open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)
@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry Polynomial TopologicalSpace
namespace AlgebraicGeometry.Scheme.OverField.Curve.ProjectiveLine
open AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

abbrev projectiveLineOver : FScheme k := Over.mk (ProjectiveLine.structureMap k)

/-- Literal polynomial P¹ and native lifted-coordinate P¹, over the original field. -/
def projectiveLineOverIsoNative :
    projectiveLineOver k ≅
      Over.mk (AlgebraicGeometry.ProjectiveSpace.toSpec k (ULift.{u} (Fin 2))) :=
  AlgebraicGeometry.ProjectiveSpace.finUliftOverIso k 2

end AlgebraicGeometry.Scheme.OverField.Curve.ProjectiveLine
end
