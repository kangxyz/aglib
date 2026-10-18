/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.IdealSheaf.LocallyClosed

/-! Focused consumer of the affine description of pulled-back ideal sheaves and of the universal
property of locally closed subschemes `V(I) \ V(J)`, with axiom guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

example {X Y : Scheme.{u}} (I : X.IdealSheafData) (g : Y ⟶ X) (U : X.affineOpens)
    (V : Y.affineOpens) (h : V.1 ≤ g ⁻¹ᵁ U.1) :
    (I.comap g).ideal V = (I.ideal U).map (g.appLE U V h).hom :=
  Scheme.IdealSheafData.ideal_comap_eq_map_appLE I g U V h

example {X Y : Scheme.{u}} (I J : X.IdealSheafData) (g : Y ⟶ X) :
    (∃ g' : Y ⟶ Scheme.IdealSheafData.locallyClosed I J,
        g' ≫ Scheme.IdealSheafData.locallyClosedι I J = g) ↔
      I.comap g = ⊥ ∧ J.comap g = ⊤ :=
  Scheme.IdealSheafData.exists_lift_locallyClosedι_iff I J g

example {X : Scheme.{u}} (I J : X.IdealSheafData) :
    IsImmersion (Scheme.IdealSheafData.locallyClosedι I J) :=
  inferInstance

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_eq_map_appLE' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_eq_map_appLE

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.exists_lift_subschemeι_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.exists_lift_subschemeι_iff

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.exists_lift_locallyClosedι_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.exists_lift_locallyClosedι_iff

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.comap_eq_bot_iff_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.comap_eq_bot_iff_forall

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.fromSpec_mem_support_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.fromSpec_mem_support_iff
