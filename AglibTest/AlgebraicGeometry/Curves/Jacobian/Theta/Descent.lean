/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Descent

/-! # The point-free original Abel difference -/

@[expose] public section

open AlgebraicGeometry.Scheme.OverField.Curve

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianDifferenceMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianDifferenceMorphism

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianDifferenceMorphism_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianDifferenceMorphism_diagonal

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianDifferenceMorphism_cocycle' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianDifferenceMorphism_cocycle

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianDifferenceFamilyClass_naturality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianDifferenceFamilyClass_naturality

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianDifferenceFamilyClass_parameter_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianDifferenceFamilyClass_parameter_one

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianDifferenceFamilySection_naturality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianDifferenceFamilySection_naturality

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianDifferenceFamilySection_parameter_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianDifferenceFamilySection_parameter_one

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianDifferenceFamilyClass_changeOrigin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianDifferenceFamilyClass_changeOrigin

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianDifferenceFamilySection_changeOrigin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianDifferenceFamilySection_changeOrigin

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalAbelPicardSection' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalAbelPicardSection

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalAbelPicardSection_pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalAbelPicardSection_pullback

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalAbelPicardSection_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalAbelPicardSection_unique

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalAbelPicardSection_map' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalAbelPicardSection_map

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalAbelPicardSection_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalAbelPicardSection_unit

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalAbelPicardMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalAbelPicardMorphism

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.homEquiv_comp_canonicalAbelPicardMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms homEquiv_comp_canonicalAbelPicardMorphism

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalAbelPicardMorphism_pointed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalAbelPicardMorphism_pointed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalAbelDualMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalAbelDualMorphism

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalAbelDualMorphism_pointed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalAbelDualMorphism_pointed

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isMonHom_canonicalAbelDualMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isMonHom_canonicalAbelDualMorphism

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalAbelDualGroupHom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalAbelDualGroupHom

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.jacobianDifferenceMorphism_eq_basedDifference' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms jacobianDifferenceMorphism_eq_basedDifference

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.canonicalAbelDualMorphism_eq_originalPullback' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms canonicalAbelDualMorphism_eq_originalPullback

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isIso_canonicalAbelDualMorphism_of_positiveGenus' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isIso_canonicalAbelDualMorphism_of_positiveGenus

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isIso_canonicalAbelDualMorphism_of_genusZero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isIso_canonicalAbelDualMorphism_of_genusZero

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.isIso_canonicalAbelDualMorphism_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isIso_canonicalAbelDualMorphism_of_isAlgClosed
