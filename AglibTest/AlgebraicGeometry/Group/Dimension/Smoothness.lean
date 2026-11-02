/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Dimension.Smoothness

/-!
# Consumer checks for smoothness from the actual regular group unit

The algebraically closed field and local finite type hypotheses remain explicit. Neither
properness nor target smoothness is supplied to the translation criterion.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.OverField

universe u

namespace AglibTest.GroupDimensionSmoothness

example {k : Type u} [Field k] [IsAlgClosed k] (G : FScheme k) [GrpObj G]
    [LocallyOfFiniteType G.hom]
    [IsRegularLocalRing (G.left.presheaf.stalk (unitPoint G))] : Smooth G.hom :=
  smooth_of_isRegularLocalRing_unit_of_isAlgClosed G

/--
info: 'AlgebraicGeometry.Scheme.Group.smooth_of_isRegularLocalRing_unit_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Group.smooth_of_isRegularLocalRing_unit_of_isAlgClosed

end AglibTest.GroupDimensionSmoothness
