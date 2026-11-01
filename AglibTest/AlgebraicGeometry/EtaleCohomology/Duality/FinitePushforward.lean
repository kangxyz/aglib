/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.FinitePushforward

/-! Level-zero and independent-universe interfaces, and approved-axiom guards. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wX wY

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f]

/-- The ordinary finite unit-Ext comparison includes level zero and independent Ext worlds. -/
example [HasExt.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod 0)))]
    [HasExt.{wY} (ModuleSheaf Y (ULift.{u + 1} (ZMod 0)))]
    (M : ModuleSheaf Y (ULift.{u + 1} (ZMod 0))) (q : ℕ) :
    Ext.{wX} (moduleUnit X (ULift.{u + 1} (ZMod 0)))
        ((moduleDirectImage f (ULift.{u + 1} (ZMod 0))).obj M) q ≃+
      Ext.{wY} (moduleUnit Y (ULift.{u + 1} (ZMod 0))) M q :=
  moduleFiniteUnitExtAddEquiv f 0 M q

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleFiniteUnitExtAddEquiv_mk₀'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleFiniteUnitExtAddEquiv_mk₀

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleFiniteUnitExtAddEquiv_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleFiniteUnitExtAddEquiv_naturality

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleFiniteUnitExtAddEquiv_eq_pullback'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleFiniteUnitExtAddEquiv_eq_pullback

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.moduleFiniteUnitExtCohomology_square'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.moduleFiniteUnitExtCohomology_square
