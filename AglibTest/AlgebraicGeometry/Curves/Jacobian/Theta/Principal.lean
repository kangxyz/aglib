/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Principal

/-! # Original conditional theta principal isomorphism interfaces -/

@[expose] public section

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isIso_thetaLineBundleMorphism_of_structureH1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.OverField.Curve.isIso_thetaLineBundleMorphism_of_structureH1_le

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.thetaPrincipalIsoOfStructureH1Le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.thetaPrincipalIsoOfStructureH1Le

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.thetaPrincipalIsoOfStructureH1Le_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.thetaPrincipalIsoOfStructureH1Le_inv
