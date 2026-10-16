/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Standard native Ext for sheaves of modules

The original abelian category of module sheaves has standard Ext in the
universe of its objects. The theorem is indexed by the native ringed site,
so it also applies when a scheme module category is unfolded to its native
`SheafOfModules` form. Ring, coefficient, site and morphism universes remain
independent.
-/

@[expose] public section

open CategoryTheory

namespace SheafOfModules

universe u v u' v'

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

/-- Native abelian module-sheaf Ext, with its original standard size bound. -/
theorem hasExt (R : Sheaf J RingCat.{u}) [Abelian (SheafOfModules.{v} R)] :
    HasExt.{max u u' v' (v + 1)} (SheafOfModules.{v} R) :=
  HasExt.standard _

end SheafOfModules
