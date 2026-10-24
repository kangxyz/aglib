/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.Noetherian.LocallyNoetherianOver
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.Fppf
public import Aglib.AlgebraicGeometry.Sites.OverRepresentability.LocallyNoetherian
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Consumer checks for fppf sheaves as Zariski sheaves over a base

The functor of points of a scheme over `S` is an fppf sheaf on `Over S` (the fppf topology is
subcanonical), so its restriction to locally Noetherian test schemes satisfies the Zariski sheaf
hypothesis of the local representability criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Scheme.LocalRepresentability

universe u

namespace AglibTest.FppfZariskiSheaf

variable {S : Scheme.{u}} (Y : Over S)

/-- The functor of points of `Y`, restricted to locally Noetherian test schemes, is a Zariski
sheaf in the sense of the local representability criterion. -/
example : IsZariskiSheaf ((Scheme.locallyNoetherianOver S).ι.op ⋙ yoneda.obj Y) :=
  isZariskiSheaf_comp_ι_of_isSheaf_fppfTopology_over
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

/--
info: 'AlgebraicGeometry.Scheme.zariskiTopology_over_le_fppfTopology_over' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Scheme.zariskiTopology_over_le_fppfTopology_over

end AglibTest.FppfZariskiSheaf
