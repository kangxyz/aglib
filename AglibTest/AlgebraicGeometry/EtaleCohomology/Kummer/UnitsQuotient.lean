/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.UnitsQuotient

/-! Interface examples and approved-foundation guards for the shared provider. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.Modules.Invertible
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u w w'

/-- The complete exact sequence has the actual torsion subgroup as its third term. -/
example (Y : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} Y)]
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(Y, ⊤))) :
    Function.Injective (Kummer.unitsQuotientBoundary Y n hn hinv) ∧
      Function.Exact (Kummer.unitsQuotientBoundary Y n hn hinv)
        (Kummer.rootsPicardTorsionMap Y n hn hinv) ∧
      Function.Surjective (Kummer.rootsPicardTorsionMap Y n hn hinv) :=
  ⟨Kummer.unitsQuotientBoundary_injective Y n hn hinv,
    Kummer.exact_unitsQuotientBoundary_rootsPicardTorsionMap Y n hn hinv,
    Kummer.rootsPicardTorsionMap_surjective Y n hn hinv⟩

/-- The geometric square admits independent source and target Ext universes. -/
example {X S : Scheme.{u}} [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)] (f : S ⟶ X)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    (Kummer.rootsPicardTorsionMap S n hn (levelInvertible f n hinv)).comp
        (Kummer.rootsCohomologyPullback f n hn hinv 1) =
      (Kummer.picardTorsionPullback f n).comp (Kummer.rootsPicardTorsionMap X n hn hinv) :=
  Kummer.rootsPicardTorsionMap_pullback f n hn hinv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.gmZeroAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.gmZeroAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsBoundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsBoundary

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsBoundary_eq_zero_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsBoundary_eq_zero_iff

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsBoundary_ker' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsBoundary_ker

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsQuotientBoundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsQuotientBoundary

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsQuotientBoundary_mk' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsQuotientBoundary_mk

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsQuotientBoundary_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsQuotientBoundary_injective

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.rootsPicardMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.rootsPicardMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.exact_unitsQuotientBoundary_rootsPicardMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.exact_unitsQuotientBoundary_rootsPicardMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.range_rootsPicardMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.range_rootsPicardMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.rootsPicardTorsionMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.rootsPicardTorsionMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.rootsPicardTorsionMap_subtype' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.rootsPicardTorsionMap_subtype

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.rootsPicardTorsionMap_surjective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.rootsPicardTorsionMap_surjective

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.exact_unitsQuotientBoundary_rootsPicardTorsionMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.exact_unitsQuotientBoundary_rootsPicardTorsionMap

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsPullback' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsPullback

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsPullback_id' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsPullback_id

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsPullback_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsPullback_comp

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsQuotientPullback' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsQuotientPullback

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsQuotientPullback_id' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsQuotientPullback_id

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsQuotientPullback_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsQuotientPullback_comp

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsQuotientPullback_mk' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsQuotientPullback_mk

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.picardTorsionPullback' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.picardTorsionPullback

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.picardTorsionPullback_subtype' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.picardTorsionPullback_subtype

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.picardTorsionPullback_id' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.picardTorsionPullback_id

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.picardTorsionPullback_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.picardTorsionPullback_comp

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.gmZeroAddEquiv_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.gmZeroAddEquiv_naturality

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.rootsPicardMap_pullback' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.rootsPicardMap_pullback

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsBoundary_pullback' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsBoundary_pullback

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsQuotientBoundary_pullback' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.unitsQuotientBoundary_pullback

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.rootsPicardTorsionMap_pullback' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.rootsPicardTorsionMap_pullback
