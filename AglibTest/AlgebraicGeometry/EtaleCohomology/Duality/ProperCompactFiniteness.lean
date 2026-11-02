/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ProperCompactFiniteness

/-! Finite original proper compact groups without general duality hypotheses. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wX wA

attribute [local instance] hasSheafifyLarge hasSheafifyModules moduleSheafExtZModModule

example {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
    [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]
    (F : ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence X.left (ULift.{u + 1} (ZMod n))).inverse.obj F)) (q : ℕ) :
    Finite (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek (𝟙 X.left) (ULift.{u + 1} (ZMod n))).obj F) q) :=
  moduleUnitCompactIdExt_finite_of_finiteLocallyConstant X hX n hn hunit F hF q

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitCompactIdExt_finite_of_finiteLocallyConstant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleUnitCompactIdExt_finite_of_finiteLocallyConstant
