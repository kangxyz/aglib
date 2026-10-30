/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Projectivity.AffineMap

/-!
# Consumer check for an affine map from a proper integral curve to the projective line

The direct lower-leaf import gives the original theorem over every field,
with only properness, integrality and dimension one; axiom guard.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AglibTest.CurvesProjectivityAffineMap

example {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [IsProper p] [IsIntegral X] (hdim : topologicalKrullDim X = 1) :
    ∃ ρ : X ⟶ Scheme.ProjectiveLine.projectiveP1 k, IsAffineHom ρ :=
  Scheme.OverField.Curve.Projectivity.exists_isAffineHom_to_projectiveP1 p hdim

end AglibTest.CurvesProjectivityAffineMap

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Projectivity.exists_isAffineHom_to_projectiveP1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.OverField.Curve.Projectivity.exists_isAffineHom_to_projectiveP1
