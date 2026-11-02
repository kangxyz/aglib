/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.AutodualityMorphism

/-! # Original theta AutodualityMorphism interfaces -/

@[expose] public section

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.thetaAutoduality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.thetaAutoduality

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.thetaAutoduality_leftInverse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.thetaAutoduality_leftInverse

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.mono_thetaLineBundleMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.mono_thetaLineBundleMorphism
