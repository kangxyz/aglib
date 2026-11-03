/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.CanonicalPrincipal

/-! # Axiom guards for the original canonical principal consumers -/

@[expose] public section

open AlgebraicGeometry.Scheme.OverField.Curve

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianStructureH1Le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianStructureH1Le

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalJacobianAbelDualMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalJacobianAbelDualMorphism

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isIso_canonicalJacobianAbelDualMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isIso_canonicalJacobianAbelDualMorphism

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalJacobianAbelDualMorphism_eq_originalPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalJacobianAbelDualMorphism_eq_originalPullback

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalJacobianPrincipalGroupIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalJacobianPrincipalGroupIso

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalJacobianPrincipalIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalJacobianPrincipalIso

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalJacobianPrincipalIso_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalJacobianPrincipalIso_hom

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalJacobianPrincipalIso_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalJacobianPrincipalIso_inv

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalJacobianPrincipalIso_inv_originalPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalJacobianPrincipalIso_inv_originalPullback

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalJacobianPrincipalIso_geometricPositive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalJacobianPrincipalIso_geometricPositive
