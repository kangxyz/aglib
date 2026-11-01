/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Ample

/-! # Original theta Ample interfaces -/

@[expose] public section

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isIso_thetaLineBundleKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.isIso_thetaLineBundleKernel

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.thetaLineBundle_isAmple' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.thetaLineBundle_isAmple
