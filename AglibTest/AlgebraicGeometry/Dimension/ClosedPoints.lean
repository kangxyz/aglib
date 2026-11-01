/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Dimension.ClosedPoints

/-! The original closed stalk computes dimension without a smoothness premise. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

example (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X)
    (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = topologicalKrullDim X :=
  Scheme.ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed k f x hx

end
