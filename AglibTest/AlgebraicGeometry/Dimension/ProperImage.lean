/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Dimension.ProperImage

/-! # Dimension of the original proper schematic image -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

example {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    topologicalKrullDim f.image ≤ topologicalKrullDim X :=
  f.topologicalKrullDim_image_le

/--
info: 'AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_image_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_image_le
