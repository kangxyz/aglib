/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Abel.EvaluationDegree

/-! # Original evaluation fibre scheme degree, with its explicit integer cast -/

@[expose] public section

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.evaluationZero_fibre_degree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Abel.evaluationZero_fibre_degree

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.rankOneEvaluation_fibre_degree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Abel.rankOneEvaluation_fibre_degree
