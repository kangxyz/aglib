/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension

/-!
# Scheme dimension and actual stalks

The dimension equality holds for every scheme, without a field, Noetherianity
or quasi-compactness premise.

Source: Aglib/AlgebraicGeometry/Morphisms/Smooth/Charts.lean:22–30 at
451aeda6b8bb5b44402b574dd6cf60f912360f8c. The complete statement and proof are unchanged.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Scheme dimension is the supremum of the dimensions of its actual local
rings. No Noetherian or quasi-compact hypothesis is used. -/
theorem topologicalKrullDim_eq_iSup_stalk (X : Scheme.{u}) :
    topologicalKrullDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := by
  simp only [ringKrullDim_stalk_eq_coheight]
  rw [topologicalKrullDim,
    Order.krullDim_eq_of_orderIso
      (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]

end AlgebraicGeometry.Scheme
