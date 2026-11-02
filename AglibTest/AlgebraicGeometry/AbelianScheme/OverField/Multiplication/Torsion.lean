/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Multiplication.Torsion

/-! The torsion description retains level one and does not impose a chosen or equivariant basis. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField

universe u

attribute [local instance] Over.cartesianMonoidalCategory

example {k : Type u} [Field k] (G : Grp (FScheme k)) [IsCommMonObj G.X]
    [IsHProjective G.X.hom] [GeometricallyIntegral G.X.hom] [Smooth G.X.hom]
    (n : ℕ) (hn : IsUnit (n : k)) :
    Nonempty (AddSubgroup.torsionBy (Scheme.Group.MultiplicationKernel.geometricPoints G) (n : ℤ) ≃+
      (Fin (2 * Module.finrank k (Cotangent.Space η[G.X])) → ZMod n)) :=
  Scheme.Group.Multiplication.nonempty_geometric_torsionEquiv_of_isUnit G n hn

example {k : Type u} [Field k] (G : Grp (FScheme k)) [IsCommMonObj G.X]
    [IsHProjective G.X.hom] [GeometricallyIntegral G.X.hom] [Smooth G.X.hom] :
    Nonempty (AddSubgroup.torsionBy (Scheme.Group.MultiplicationKernel.geometricPoints G) (1 : ℤ) ≃+
      (Fin (2 * Module.finrank k (Cotangent.Space η[G.X])) → ZMod 1)) :=
  Scheme.Group.Multiplication.nonempty_geometric_torsionEquiv_of_isUnit G 1 (by simp)

end
