/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Multiplication.FiniteKernel

/-! The native finite-kernel criterion has no scalar-invertibility condition. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

attribute [local instance] Over.cartesianMonoidalCategory

example {k : Type u} [Field k] (G : Grp (Over (Spec (.of k))))
    [IsCommMonObj G.X] [IsProper G.X.hom] [GeometricallyIntegral G.X.hom]
    (n : ℕ) [IsFinite (Scheme.Group.MultiplicationKernel.kernelGroup G n).X.hom] :
    IsFinite ((𝟙 G.X) ^ n).left ∧ Flat ((𝟙 G.X) ^ n).left ∧
      Surjective ((𝟙 G.X) ^ n).left :=
  Scheme.Group.Multiplication.multiplication_finite_flat_surjective_of_finite_kernelGroup G n

end
