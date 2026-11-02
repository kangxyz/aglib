/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Dimension.FiniteFibreImage

/-! # Actual finite fibres and proper image dimension, without separability -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

example {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n p]
    (f : X ⟶ Y) [IsProper f] (x : X) (hx : (f ⁻¹' {f x}).Finite) :
    topologicalKrullDim f.image = n :=
  Scheme.Hom.topologicalKrullDim_image_eq_of_smooth_of_finite_fibre p n f x hx

/--
info: 'AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_image_eq_of_smooth_of_finite_fibre' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_image_eq_of_smooth_of_finite_fibre
