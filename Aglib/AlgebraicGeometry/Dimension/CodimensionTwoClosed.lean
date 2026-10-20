/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Dimension.CodimensionTwo

/-!
# Closed codimension-two points

This index retains both the stalk dimension and closedness of the actual point.
It is the literal subtype used by the incoming coherent support residue and
surface suppliers at R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Codimension-two points without a closedness proof remain a separate index.
-/

@[expose] public section
open AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme
universe u

/-- An actual point with stalk dimension two and its explicit closedness proof. -/
abbrev CodimensionTwoClosedPoint (X : Scheme.{u}) :=
  { x : X // ringKrullDim (X.presheaf.stalk x) = 2 ∧ IsClosed ({x} : Set X) }

end AlgebraicGeometry.Scheme
