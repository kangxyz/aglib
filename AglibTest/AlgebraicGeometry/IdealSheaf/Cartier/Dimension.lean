/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Dimension

/-! # Actual height-one stalk kernels and Cartier ideals from dimension -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

example {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y] [IsLocallyNoetherian Y]
    (i : C ⟶ Y) [IsClosedImmersion i]
    (hregular : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (n : ℕ) (hC : topologicalKrullDim C = n)
    (hY : topologicalKrullDim Y ≤ (n : WithBot ℕ∞) + 1)
    (hrange : Set.range i ≠ Set.univ) : Scheme.Hom.IsEffectiveCartier i :=
  Scheme.Hom.isEffectiveCartier_of_dimension i hregular n hC hY hrange

/--
info: 'AlgebraicGeometry.Scheme.Hom.isEffectiveCartier_of_dimension' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Hom.isEffectiveCartier_of_dimension
