/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Multiplication.Finite
/-! All-positive-level conclusions retain characteristic-dividing levels. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

attribute [local instance] Over.cartesianMonoidalCategory

example {k : Type u} [Field k] (G : Grp (Over (Spec (.of k))))
    [IsCommMonObj G.X] [IsHProjective G.X.hom] [GeometricallyIntegral G.X.hom]
    (n : ℕ) (hn : 0 < n) :
    IsFinite ((𝟙 G.X) ^ n).left ∧ Flat ((𝟙 G.X) ^ n).left ∧
      Surjective ((𝟙 G.X) ^ n).left :=
  Scheme.Group.Multiplication.multiplication_finite_flat_surjective_of_isHProjective G n hn

end
