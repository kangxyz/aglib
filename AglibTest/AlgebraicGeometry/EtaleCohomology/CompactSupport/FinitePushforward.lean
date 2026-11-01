/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FinitePushforward

/-! Finite Cartesian support interfaces and approved-axiom guards. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients

universe u wX wY
variable {V U Y X : Scheme.{u}} (p : Y ⟶ X) [IsFinite p]
  (f : V ⟶ U) (jU : U ⟶ X) [IsOpenImmersion jU]
  (jV : V ⟶ Y) [IsOpenImmersion jV] (h : IsPullback jV f p jU)

/-- The finite Cartesian extension comparison imposes no étaleness or flatness on p. -/
example : directImage f ⋙ etaleLowerShriek jU ≅ etaleLowerShriek jV ⋙ directImage p :=
  finiteLowerShriekDirectImageIso p f jU jV h

/-- The original roots unit defines compact pullback at zero in independent Ext worlds. -/
example [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{wY} (AbelianSheaf.{u, u + 1} Y)] (q : ℕ) :
    CompactSupport.H jU (mu U 0) q →+ CompactSupport.H jV (mu V 0) q :=
  CompactSupport.finiteRootsPullbackMap p f jU jV h 0 q

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.finiteOpenCounit_isIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.finiteOpenCounit_isIso

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.finiteOpenRestrictionIso_inv_baseChange'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.finiteOpenRestrictionIso_inv_baseChange

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.finiteLowerShriekDirectImageMap_unit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.finiteLowerShriekDirectImageMap_unit

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.finiteLowerShriekDirectImageMap_isIso'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.finiteLowerShriekDirectImageMap_isIso

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.finiteLowerShriekDirectImageMap_roots_unit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.finiteLowerShriekDirectImageMap_roots_unit

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.finiteDirectImageAddEquiv_naturality'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.finiteDirectImageAddEquiv_naturality

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.finiteRootsTraceMap_comp_finiteRootsPullbackMap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.finiteRootsTraceMap_comp_finiteRootsPullbackMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.finiteRootsTraceMap_level'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.finiteRootsTraceMap_level
