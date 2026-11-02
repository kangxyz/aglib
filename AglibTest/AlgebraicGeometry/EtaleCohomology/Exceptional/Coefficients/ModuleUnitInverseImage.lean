/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ModuleUnitInverseImage

/-!
# Tests for the inverse image of the rank-one module sheaf `ℤ/n`

The examples restate `jV^* (ℤ/n)_U ≅ (ℤ/n)_V` among module sheaves for an open immersion
`jV : V ⟶ U`, with its underlying isomorphism, and guard the axioms of every new declaration.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

namespace AglibTest.EtaleDualityModuleUnitInverseImage

attribute [local instance] hasSheafifyLarge

variable {V U : Scheme.{u}} (jV : V ⟶ U) [IsOpenImmersion jV] (n : ℕ)

/-- The restriction of `ℤ/n` to an open subscheme is `ℤ/n`. -/
example :
    (moduleInverseImage jV (ULift.{u + 1} (ZMod n))).obj
        (moduleUnit U (ULift.{u + 1} (ZMod n))) ≅
      moduleUnit V (ULift.{u + 1} (ZMod n)) :=
  moduleUnitInverseImageIso jV n

example :
    (SheafOfModules.toSheaf (constantRing V (ULift.{u + 1} (ZMod n)))).map
        (moduleUnitInverseImageIso jV n).hom =
      (moduleInverseImageUnderlyingIso (ULift.{u + 1} (ZMod n)) jV).hom.app
          (moduleUnit U (ULift.{u + 1} (ZMod n))) ≫
        (inverseImage jV).map (moduleUnitUnderlyingIso U (ULift.{u + 1} (ZMod n))).inv ≫
          (inverseImageConstantIso jV).hom.app (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) ≫
            (moduleUnitUnderlyingIso V (ULift.{u + 1} (ZMod n))).hom :=
  moduleUnitInverseImageIso_underlying jV n

end AglibTest.EtaleDualityModuleUnitInverseImage

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitInverseImageIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitInverseImageIso

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitInverseImageIso_underlying' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitInverseImageIso_underlying

