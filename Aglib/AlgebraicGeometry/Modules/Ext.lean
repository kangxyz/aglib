/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Ext

/-!
# The standard Ext universe for actual scheme module sheaves

For a scheme in universe `u`, native module-sheaf Ext groups are taken in
`Type (u + 1)`, using the original standard derived-category construction.
This matches the existing additive-sheaf cohomology universe and requires
no resizing or finiteness hypothesis.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Native scheme module-sheaf Ext has the same standard size as additive cohomology. -/
instance hasExt (X : Scheme.{u}) : HasExt.{u + 1} X.Modules :=
  SheafOfModules.hasExt X.ringCatSheaf

/-- The same standard instance on the literal native module-sheaf category. -/
instance hasExtSheafOfModules (X : Scheme.{u}) :
    HasExt.{u + 1} (SheafOfModules.{u} X.ringCatSheaf) :=
  hasExt X

end AlgebraicGeometry.Scheme.Modules
