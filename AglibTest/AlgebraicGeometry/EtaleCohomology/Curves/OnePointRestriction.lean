/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.OnePointRestriction

/-! # Actual Kummer restriction across one point, with independent cohomology sizes -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.EtaleCohomology

universe u wX wV

attribute [local instance] hasSheafifyLarge

example {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
    (x : Scheme.ClosedPoint X.left) (V : X.left.Opens)
    (hV : (V : Set X.left) = {x.val}ᶜ)
    [HasExt.{wX} (AbelianSheaf.{u, u + 1} X.left)]
    [HasExt.{wV} (AbelianSheaf.{u, u + 1} V.toScheme)]
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X.left, ⊤))) :
    Function.Bijective (GroupCohomology.Kummer.CoefficientBaseChange.h1Map V.ι n hn hinv) :=
  Curves.rootsH1Restriction_bijective_of_onePoint hX x V hV n hn hinv

example {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
    (x : Scheme.ClosedPoint X.left) (V : X.left.Opens)
    (hV : (V : Set X.left) = {x.val}ᶜ)
    [HasExt.{wX} (AbelianSheaf.{u, u + 1} X.left)]
    [HasExt.{wV} (AbelianSheaf.{u, u + 1} V.toScheme)]
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    (hinv : IsUnit (n : Γ(X.left, ⊤))) (q : ℕ) (hq : q ≤ 1) :
    Function.Bijective (Kummer.rootsCohomologyPullback V.ι n hn hinv q) :=
  Curves.rootsCohomologyPullback_bijective_of_onePoint_of_le_one hX x V hV n hn hunit hinv q hq

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.rootsH1Restriction_bijective_of_onePoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.rootsH1Restriction_bijective_of_onePoint

/--
info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Curves.rootsCohomologyPullback_bijective_of_onePoint_of_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Curves.rootsCohomologyPullback_bijective_of_onePoint_of_le_one
