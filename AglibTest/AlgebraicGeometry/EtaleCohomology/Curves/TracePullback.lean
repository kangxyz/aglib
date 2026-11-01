/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.TracePullback

/-! Original normalized trace maps and approved-axiom guards. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u wX wY

variable {V U Y X : Scheme.{u}} (p : Y ⟶ X) [IsFinite p]
  (f : V ⟶ U) (jU : U ⟶ X) [IsOpenImmersion jU]
  (jV : V ⟶ Y) [IsOpenImmersion jV] (h : IsPullback jV f p jU)
  [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wY} (AbelianSheaf.{u, u + 1} Y)]

/-- The compact/proper square requires no étaleness or flatness of the completion map. -/
example (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (q : ℕ) :
    (CompactSupport.rootsMap jV n hn (levelInvertible p n hinv) q).comp
        (CompactSupport.finiteRootsPullbackMap p f jU jV h n q) =
      (Kummer.rootsCohomologyPullback p n hn hinv q).comp
        (CompactSupport.rootsMap jU n hn hinv q) :=
  CompactSupport.rootsMap_finiteRootsPullback p f jU jV h n hn hinv q

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsExtensionMap_level'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsExtensionMap_level

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsMap_finiteRootsPullback'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport.rootsMap_finiteRootsPullback

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.traceAddEquiv_level' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.traceAddEquiv_level

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.compactSupportTraceAddEquiv_level'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.compactSupportTraceAddEquiv_level

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.traceAddEquiv_pullback_of_hasLocallyFreeRank'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.traceAddEquiv_pullback_of_hasLocallyFreeRank

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.compactSupportTraceAddEquiv_finitePullback_of_hasLocallyFreeRank'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.compactSupportTraceAddEquiv_finitePullback_of_hasLocallyFreeRank

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.traceAddEquiv_pullback_of_functionField_finite'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.traceAddEquiv_pullback_of_functionField_finite

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.compactSupportTraceAddEquiv_finiteRootsTrace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.compactSupportTraceAddEquiv_finiteRootsTrace
