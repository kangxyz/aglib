/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Actual closed scheme points
-/

@[expose] public section


open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme
universe u
/-- Actual scheme points whose singleton is closed. -/
def ClosedPoint (X : Scheme.{u}) := {x : X // IsClosed ({x} : Set X)}

end AlgebraicGeometry.Scheme

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Points/Closed.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 f44d82e89c2f371b380f3d7d11b8143741169cda8cf4711cb34812f5fff2be7f.
Native names and imports replace source wrappers; stated conditions and maps are retained. -/
