/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Descent.GroundAmple
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Descent.GroundPolarization

/-! Axiom boundary for the original ground-field ample theta polarization. -/

open AlgebraicGeometry.Scheme.OverField.Curve

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.thetaLineBundleGroundField_isAmple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms thetaLineBundleGroundField_isAmple

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.lineBundleClassMorphismIdentityComponent_thetaLineBundleGroundField' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms lineBundleClassMorphismIdentityComponent_thetaLineBundleGroundField
