/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ModuleUnitUnderlying

/-!
# Tests for the underlying abelian sheaf of the rank-one module sheaf

The examples restate that the underlying abelian sheaf of `Λ_U` is the constant sheaf `Λ`, and
for `Λ = ULift (ZMod n)` the constant finite coefficient `ℤ/n`, and guard the axioms of every
new declaration.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

namespace AglibTest.EtaleDualityModuleUnitUnderlying

attribute [local instance] hasSheafifyLarge

variable (U : Scheme.{u}) (n : ℕ)

/-- The underlying abelian sheaf of `ℤ/n` as a module sheaf is the constant sheaf `ℤ/n`. -/
example :
    ConstantFinite.coefficient (ULift.{u} (ZMod n)) U ≅
      (SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj
        (moduleUnit U (ULift.{u + 1} (ZMod n))) :=
  moduleUnitCoefficientIso U n

/-- For an arbitrary ring, the underlying abelian sheaf of `Λ_U` is the constant sheaf `Λ`. -/
example (Λ : Type (u + 1)) [Ring Λ] :
    (constantSheaf (Scheme.smallEtaleTopology U) AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of Λ) ≅
      (SheafOfModules.toSheaf (constantRing U Λ)).obj (moduleUnit U Λ) :=
  moduleUnitUnderlyingIso U Λ

end AglibTest.EtaleDualityModuleUnitUnderlying

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitConstantMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitConstantMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitConstantMap_whiskerRight_forget' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitConstantMap_whiskerRight_forget

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitConstantMap_isLocallyInjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitConstantMap_isLocallyInjective

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitConstantMap_isLocallySurjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitConstantMap_isLocallySurjective

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitConstantMap_presheafToSheaf_map_isIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitConstantMap_presheafToSheaf_map_isIso

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitUnderlyingIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitUnderlyingIso

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitCoefficientIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitCoefficientIso
