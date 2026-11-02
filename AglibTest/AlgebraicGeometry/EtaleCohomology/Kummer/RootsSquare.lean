/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsSquare

/-! The commutative-square interface has no Cartesian or flatness premise. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u
variable {Y X V U : Scheme.{u}}
  (p : Y ⟶ X) (f : V ⟶ U) (jU : U ⟶ X) (jV : V ⟶ Y)
  (h : f ≫ jU = jV ≫ p)

/-- Positive invertible level one is included with the original square comparison. -/
example (hunit : IsUnit (1 : Γ(X, ⊤))) :
    (inverseImageSquareIso p f jU jV h).hom.app (mu X 1) ≫
        (inverseImage jV).map (rootsPullbackIso p 1 Nat.zero_lt_one
          (by simpa only [Nat.cast_one] using hunit)).hom ≫
        (rootsPullbackIso jV 1 Nat.zero_lt_one
          (levelInvertible p 1 (by simpa only [Nat.cast_one] using hunit))).hom =
      (inverseImage f).map (rootsPullbackIso jU 1 Nat.zero_lt_one
        (by simpa only [Nat.cast_one] using hunit)).hom ≫
        (rootsPullbackIso f 1 Nat.zero_lt_one
          (levelInvertible jU 1 (by simpa only [Nat.cast_one] using hunit))).hom :=
  rootsPullbackIso_square p f jU jV h 1 Nat.zero_lt_one
    (by simpa only [Nat.cast_one] using hunit)

/-- info: 'GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso_square' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso_square

/-- info: 'GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso_square_inv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GroupCohomology.Kummer.CoefficientBaseChange.rootsPullbackIso_square_inv
