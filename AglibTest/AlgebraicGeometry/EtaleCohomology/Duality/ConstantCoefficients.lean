/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ConstantCoefficients

/-! Original-map examples and approved-axiom guards. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

attribute [local instance] hasSheafifyLarge moduleSheafExtZModModule

universe u w
/-- The original scalar identity is intrinsic on every connected scheme. -/
example (U : Scheme.{u}) [ConnectedSpace U] (n : ℕ) [NeZero n]
    [HasExt.{w} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))] :
    Function.Bijective (moduleUnitScalarLinearMap U n) :=
  moduleUnitScalarLinearMap_bijective U n

/-- The original unit and root module sheaves are isomorphic over the algebraically closed base. -/
example (k : Type u) [Field k] [IsAlgClosed k] {U : Scheme.{u}}
    (p : U ⟶ Spec (.of k)) (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : k)) :
    Nonempty (moduleUnit U (ULift.{u + 1} (ZMod n)) ≅ moduleRootsOfUnity U n) :=
  ⟨moduleUnitRootsIso k n hn hu p⟩

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitRootsIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitRootsIso

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitRootsIso_underlying' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitRootsIso_underlying

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnit_nsmul_id_bijective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnit_nsmul_id_bijective

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitScalarLinearMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitScalarLinearMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitScalarLinearMap_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitScalarLinearMap_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitScalarLinearMap_apply_eq_mk₀_nsmul' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitScalarLinearMap_apply_eq_mk₀_nsmul

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitScalarLinearMap_bijective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitScalarLinearMap_bijective

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitIsoScalarMap_bijective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitIsoScalarMap_bijective

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitScalarLinearMap_cohomology' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitScalarLinearMap_cohomology
