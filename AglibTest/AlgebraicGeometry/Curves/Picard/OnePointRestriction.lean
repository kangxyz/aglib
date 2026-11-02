/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.OnePointRestriction

/-! # The actual single-point Picard restriction kernel -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField.Curve.Picard.OnePointRestriction

universe u

example {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
    (x : Scheme.ClosedPoint X.left) (V : X.left.Opens)
    (hV : (V : Set X.left) = {x.val}ᶜ) (c : PicardGroup X.left) :
    pullbackClass V.ι c = 0 ↔ ∃ m : ℤ, c = m • closedPointClass hX x :=
  pullbackClass_eq_zero_iff_exists_zsmul_closedPointClass hX x V hV c

example {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
    (x : Scheme.ClosedPoint X.left) (V : X.left.Opens)
    (hV : (V : Set X.left) = {x.val}ᶜ) (n : ℕ) (hn : 0 < n) :
    Function.Bijective (torsionPullback V.ι n) :=
  torsionPullback_bijective hX x V hV n hn

example {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
    (x : Scheme.ClosedPoint X.left) (V : X.left.Opens)
    (hV : (V : Set X.left) = {x.val}ᶜ) :
    Function.Bijective (Units.map V.ι.appTop.hom.toMonoidHom) :=
  globalUnits_appTop_bijective hX x V hV

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Picard.OnePointRestriction.pullbackClass_eq_zero_iff_exists_zsmul_closedPointClass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Picard.OnePointRestriction.pullbackClass_eq_zero_iff_exists_zsmul_closedPointClass

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Picard.OnePointRestriction.globalUnits_appTop_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Picard.OnePointRestriction.globalUnits_appTop_bijective

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Picard.OnePointRestriction.torsionPullback_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Picard.OnePointRestriction.torsionPullback_bijective
