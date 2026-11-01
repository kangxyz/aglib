/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.OriginIndependence

/-! # The whole original Abel-origin comparison -/

@[expose] public section

open AlgebraicGeometry.Scheme.OverField.Curve

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianCurveMorphism_changeOrigin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianCurveMorphism_changeOrigin

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardIdentityComponentPullback_jacobianCurveMorphism_changeOrigin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  picardIdentityComponentPullback_jacobianCurveMorphism_changeOrigin

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.thetaPrincipalIsoOfStructureH1Le_changeOrigin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  thetaPrincipalIsoOfStructureH1Le_changeOrigin
