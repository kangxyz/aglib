/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# The standard native derived category of scheme module sheaves

Relocated from `Modules/Perfect/Local.lean` at Aglib
`451aeda6b8bb5b44402b574dd6cf60f912360f8c`, SHA-256
`a1346cd033c102625457bd3984e34fddf41385043796e00e50953593f5f71ea3`.
The local choice retains the native category and morphism universe `u + 1`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Use the constructed native derived category in morphism universe `u + 1`. -/
local instance standardHasDerivedCategory (X : Scheme.{u}) : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

end AlgebraicGeometry.Scheme.Modules
