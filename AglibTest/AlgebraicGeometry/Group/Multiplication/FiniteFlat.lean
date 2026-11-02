/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Multiplication.FiniteFlat

/-! The finite-flat consumer retains the actual positive-characteristic map. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

example {k : Type u} [Field k] (G H : Grp (Over (Spec (.of k))))
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
    [GeometricallyIntegral H.X.hom] (f : G ⟶ H)
    [IsFinite f.hom.hom.left] [Surjective f.hom.hom.left] :
    Scheme.Hom.FiniteLocallyFree f.hom.hom.left :=
  Scheme.Group.finite_surjective_hom_finiteLocallyFree G H f

end
