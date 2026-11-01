/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.LevelMaps

/-! Original coefficient maps at zero, one and composite levels, and approved-axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange
open AlgebraicGeometry.Scheme.EtaleCohomology

universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- The coefficient-level unit square needs neither positivity nor invertibility. -/
example : rootsLevelMap X 0 0 ≫ rootsUnit f 0 =
    rootsUnit f (0 * 0) ≫ (directImage f).map (rootsLevelMap Y 0 0) :=
  rootsLevelMap_unit f 0 0

/-- Level one retains the original equality transport. -/
example : rootsLevelMap X 1 1 = eqToHom (congrArg (mu X) (one_mul 1)) :=
  rootsLevelMap_one X 1

/-- Composite multipliers compose through the original arithmetic transport. -/
example : rootsLevelMap X 6 (4 * 9) ≫ rootsLevelMap X 4 9 =
    eqToHom (congrArg (mu X) (Nat.mul_assoc 6 4 9).symm) ≫ rootsLevelMap X (6 * 4) 9 :=
  rootsLevelMap_comp X 6 4 9

/-- info: 'GroupCohomology.Kummer.Coefficients.rootsLevelMap_inclusion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GroupCohomology.Kummer.Coefficients.rootsLevelMap_inclusion

/-- info: 'GroupCohomology.Kummer.Coefficients.rootsLevelMap_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GroupCohomology.Kummer.Coefficients.rootsLevelMap_comp

/-- info: 'GroupCohomology.Kummer.CoefficientBaseChange.rootsLevelMap_unit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GroupCohomology.Kummer.CoefficientBaseChange.rootsLevelMap_unit

/-- info: 'GroupCohomology.Kummer.CoefficientBaseChange.rootsLevelMap_pullback' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GroupCohomology.Kummer.CoefficientBaseChange.rootsLevelMap_pullback

/-- info: 'GroupCohomology.Kummer.CoefficientBaseChange.rootsLevelMap_pullback_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GroupCohomology.Kummer.CoefficientBaseChange.rootsLevelMap_pullback_inv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.boundary_level' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.boundary_level

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.picardBoundary_level' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.picardBoundary_level
