/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.Properties.IrreducibleComponents

/-!
A term of the original `NormalComponentsOpen` interface. The mathematical
supplier is the existing local-Noetherian component theorem in
`Aglib.AlgebraicGeometry.Properties.Normal.StalkComponents`; no global finiteness
hypothesis is added.

Basis: project 1e2b2a1a27c19ecbb9575ef9eeb57d0ae46f520e;
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612; Lean 4.34.1.
-/

@[expose] public section

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

theorem normalComponentsOpen : NormalComponentsOpen.{u} := by
  intro X hNoetherian hNormal Z hZ
  let : IsLocallyNoetherian X := hNoetherian
  let (x : X) : IsDomain (X.presheaf.stalk x) := (hNormal x).1
  exact isOpen_irreducibleComponent_of_isLocallyNoetherian_of_isDomain_stalk hZ

/-- Exercise the original connected-normal consumer at its exact interface. -/
theorem isIntegral_of_connected_normalStalks_actual
    (X : Scheme.{u}) [IsLocallyNoetherian X] [ConnectedSpace X]
    (h : NormalStalks X) : IsIntegral X :=
  isIntegral_of_connected_normalStalks normalComponentsOpen X h

end AlgebraicGeometry.Scheme
