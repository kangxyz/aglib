/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Finite.ModuleComparison

/-! The same original comparison at levels zero and one, and its whole underlying law. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f] [IsSeparated f]

example : moduleLowerShriek f (ULift.{u + 1} (ZMod 0)) ⟶
    moduleDirectImage f (ULift.{u + 1} (ZMod 0)) :=
  moduleEtaleLowerShriekToDirectImage f 0

example : moduleLowerShriek f (ULift.{u + 1} (ZMod 1)) ⟶
    moduleDirectImage f (ULift.{u + 1} (ZMod 1)) :=
  moduleEtaleLowerShriekToDirectImage f 1

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleEtaleLowerShriekToDirectImage_underlying'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleEtaleLowerShriekToDirectImage_underlying

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleFiniteEtaleLowerShriekToDirectImage_isIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleFiniteEtaleLowerShriekToDirectImage_isIso
