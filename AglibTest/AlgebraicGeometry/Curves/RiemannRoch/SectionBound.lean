/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.RiemannRoch.SectionBound

/-! # The original quotient-degree section bound with residue weights retained -/

@[expose] public section

open AlgebraicGeometry Scheme Scheme.OverField Scheme.Cohomology Curve.Divisors
open Curve.Picard Curve.Picard.DivisorClass

universe u

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
example {k : Type u} [Field k] (X : FScheme k)
    [IsIntegral X.left] [IsNoetherian X.left] [LocallyOfFiniteType X.hom]
    [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]
    (hdim : topologicalKrullDim X.left ≤ 1) {A B : Divisor X.left} (hAB : A ≤ B)
    [Subsingleton (moduleCohomology k X (divisorSheaf X.left A) 0)] :
    (Module.finrank k (moduleCohomology k X (divisorSheaf X.left B) 0) : ℤ) ≤
      Degree.degDiv X.left X.hom (B - A) :=
  divisorH0_finrank_le_quotientDegree X hdim hAB

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorH0_finrank_le_quotientDegree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass.divisorH0_finrank_le_quotientDegree
