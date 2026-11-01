/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.EffectiveClass.Uniqueness

/-! # Effective-divisor uniqueness retains actual Picard classes and field scalars -/

@[expose] public section

open AlgebraicGeometry Scheme Scheme.OverField Scheme.Cohomology
open Curve.Divisors Curve.Picard Curve.Picard.DivisorClass

universe u

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
example {k : Type u} [Field k] (X : FScheme k) [IsIntegral X.left] [IsNoetherian X.left]
    [∀ x : ClosedPoint X.left, IsDiscreteValuationRing (X.left.presheaf.stalk x.val)]
    (hdim : topologicalKrullDim X.left ≤ 1) (D E : Divisor X.left)
    (hD : ∀ x, 0 ≤ D x) (hE : ∀ x, 0 ≤ E x)
    (hclass : divisorToPicard X.left hdim D = divisorToPicard X.left hdim E)
    (h0 : Module.finrank k (moduleCohomology k X (divisorSheaf X.left D) 0) = 1) : D = E :=
  effective_divisor_eq_of_class_eq_of_h0_one X hdim D E hD hE hclass h0

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Picard.effective_divisor_eq_of_class_eq_of_h0_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Picard.effective_divisor_eq_of_class_eq_of_h0_one
