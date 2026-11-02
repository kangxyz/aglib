/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Multiplication.Degree

/-! Infinite-field multiplication uses the original power map and actual identity dimension. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField

universe u

attribute [local instance] Over.cartesianMonoidalCategory

example {k : Type u} [Field k] [Infinite k]
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
    [IsHProjective G.X.hom] [GeometricallyIntegral G.X.hom] [Smooth G.X.hom]
    (n : ℕ) (hn : 0 < n) :
    Scheme.Hom.HasLocallyFreeRank ((𝟙 G.X) ^ n).left
      (n ^ (2 * Module.finrank k (Cotangent.Space η[G.X]))) :=
  Scheme.Group.Multiplication.multiplication_hasLocallyFreeRank_of_infinite G n hn

end
