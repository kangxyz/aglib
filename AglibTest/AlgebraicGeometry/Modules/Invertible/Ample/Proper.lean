/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Ample.Proper

/-! # Proper ample-trivial finiteness with the original scheme and bundle -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AglibTest.AmpleProper

/-- No reducedness, connectedness, smoothness or dimension premise is needed. -/
example {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [IsProper p]
    (L : LineBundle X) (hL : L.IsAmple) (h0 : classOf X L = 0) : IsFinite p :=
  hL.isFinite_of_isProper_of_classOf_eq_zero p h0

/-- The original pulled-back bundle is ample on every closed subscheme. -/
example {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (L : LineBundle Y) (hL : L.IsAmple) : (pullbackLineBundle i L).IsAmple :=
  hL.pullback_of_isAffineHom i

/-- The same ample-trivial premise gives quasi-affineness without properness. -/
example {X : Scheme.{u}} (L : LineBundle X) (hL : L.IsAmple)
    (h0 : classOf X L = 0) : X.IsQuasiAffine :=
  hL.isQuasiAffine_of_classOf_eq_zero h0

end AglibTest.AmpleProper

/--
info: 'AlgebraicGeometry.Scheme.isFinite_of_isProper_of_isQuasiAffine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.isFinite_of_isProper_of_isQuasiAffine

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.LineBundle.IsAmple.isFinite_of_isProper_of_classOf_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Invertible.LineBundle.IsAmple.isFinite_of_isProper_of_classOf_eq_zero
