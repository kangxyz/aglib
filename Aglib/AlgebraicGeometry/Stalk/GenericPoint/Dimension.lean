/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.GenericPoint
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.Tactic.NormNum

/-! # Dimension -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- An original stalk of dimension two cannot be the integral scheme's generic field stalk. -/
theorem ne_genericPoint_of_stalk_dimension_two {X : Scheme.{u}} [IsIntegral X]
    (x : X) (hd : ringKrullDim (X.presheaf.stalk x) = 2) : x ≠ genericPoint X := by
  intro h
  subst x
  change ringKrullDim X.functionField = 2 at hd
  rw [ringKrullDim_eq_zero_of_field] at hd
  norm_num at hd

end AlgebraicGeometry.Scheme
