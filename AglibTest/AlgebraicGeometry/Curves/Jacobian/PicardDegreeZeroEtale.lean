/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.PicardDegreeZeroEtale

/-! Axiom guards for the original étale Jacobian inclusion and multiplication. -/

open AlgebraicGeometry.Scheme.OverField.Curve

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardDegreeZeroEtaleInclusionMono'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms picardDegreeZeroEtaleInclusionMono

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.epi_nsmul_representedJacobianBaseChange'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms epi_nsmul_representedJacobianBaseChange

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardDegreeZeroEtaleInclusionAppOfPoint'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms picardDegreeZeroEtaleInclusionAppOfPoint
