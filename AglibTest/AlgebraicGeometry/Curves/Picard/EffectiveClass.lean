/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.EffectiveClass

/-! # Actual nonzero sections and effectivity, without a genus inequality -/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry Scheme Scheme.Modules.Invertible
open Scheme.OverField.Curve Scheme.OverField.Curve.Picard

universe u

example (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (hdim : topologicalKrullDim X ≤ 1) (L : LineBundle X) :
    (∃ s : L.val.val.obj (op ⊤), s ≠ 0) ↔
      ∃ D : Divisors.Divisor X, (∀ x, 0 ≤ D x) ∧
        DivisorClass.divisorToPicard X hdim D = classOf X L :=
  exists_nonzero_section_iff_effective_class X hdim L

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Picard.exists_nonzero_section_iff_effective_class' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Picard.exists_nonzero_section_iff_effective_class
