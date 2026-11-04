/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Descent.BasedCartier

/-! Axiom boundary for the original ground-field theta classes. -/

open AlgebraicGeometry.Scheme.OverField.Curve

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.pullbackClass_intrinsicThetaLineBundleOnPicard_fieldBaseChange' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pullbackClass_intrinsicThetaLineBundleOnPicard_fieldBaseChange

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.pullbackClass_intrinsicThetaLineBundleOnPicard_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms pullbackClass_intrinsicThetaLineBundleOnPicard_translation
