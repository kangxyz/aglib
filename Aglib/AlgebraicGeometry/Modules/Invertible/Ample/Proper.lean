/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Ample.Basic
public import Aglib.AlgebraicGeometry.Morphisms.Proper.QuasiAffine

/-! # Proper schemes with an ample trivial line bundle are finite -/

@[expose] public section

namespace AlgebraicGeometry.Scheme.Modules.Invertible

universe u

/-- A scheme proper over a Noetherian affine base with ample trivial bundle
is finite over that same base. Nonreduced schemes are included. -/
theorem LineBundle.IsAmple.isFinite_of_isProper_of_classOf_eq_zero
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsProper p]
    {L : LineBundle X} (hL : L.IsAmple) (h : classOf X L = 0) : IsFinite p := by
  let : X.IsQuasiAffine := hL.isQuasiAffine_of_classOf_eq_zero h
  exact Scheme.isFinite_of_isProper_of_isQuasiAffine p

end AlgebraicGeometry.Scheme.Modules.Invertible
