/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Dimension.Finite
public import Aglib.AlgebraicGeometry.Stalk.Dimension

/-! # Stalk dimensions under finite morphisms -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- Every original source stalk of a finite morphism has dimension at most
the topological dimension of its target. -/
theorem Hom.stalk_dimension_le_of_finite
    {N Y : Scheme.{u}} (ν : N ⟶ Y) [IsFinite ν] (n : N) :
    ringKrullDim (N.presheaf.stalk n) ≤ topologicalKrullDim Y := by
  have hn : ringKrullDim (N.presheaf.stalk n) ≤ topologicalKrullDim N := by
    rw [topologicalKrullDim_eq_iSup_stalk]
    exact le_iSup (fun x : N => ringKrullDim (N.presheaf.stalk x)) n
  exact hn.trans ν.topologicalKrullDim_le_of_isFinite

/-- Compatibility name for the original finite-morphism dimension bound. -/
theorem Hom.topologicalKrullDim_le_of_finite
    {N Y : Scheme.{u}} (ν : N ⟶ Y) [IsFinite ν] :
    topologicalKrullDim N ≤ topologicalKrullDim Y :=
  ν.topologicalKrullDim_le_of_isFinite

end AlgebraicGeometry.Scheme
