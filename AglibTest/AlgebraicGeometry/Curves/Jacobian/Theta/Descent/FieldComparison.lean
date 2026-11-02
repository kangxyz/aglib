/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Descent.FieldComparison

/-! # Original graph and Picard scalar comparison -/

@[expose] public section

open AlgebraicGeometry.Scheme.OverField.Curve

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.positiveGraphClass_fieldBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms positiveGraphClass_fieldBaseChange

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.positiveCurveMorphism_baseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms positiveCurveMorphism_baseChange

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianScalarExtensionIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianScalarExtensionIso

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianScalarExtensionIso_hom_comp_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianScalarExtensionIso_hom_comp_inclusion

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.structureH1Le_jacobian_fieldBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms structureH1Le_jacobian_fieldBaseChange

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianDifferenceMorphism_baseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianDifferenceMorphism_baseChange

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianDifferenceMorphism_baseChange_universal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianDifferenceMorphism_baseChange_universal

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.structureH1Le_nativeJacobian_fieldBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms structureH1Le_nativeJacobian_fieldBaseChange


/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isIso_canonicalAbelDualMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isIso_canonicalAbelDualMorphism

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalThetaPrincipalGroupIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalThetaPrincipalGroupIso

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalThetaPrincipalIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalThetaPrincipalIso

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalThetaPrincipalIso_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalThetaPrincipalIso_hom

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalThetaPrincipalIso_geometricPositive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalThetaPrincipalIso_geometricPositive
