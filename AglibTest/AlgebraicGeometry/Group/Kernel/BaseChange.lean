/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.BaseChange

/-! Native verification of the actual kernel comparison over arbitrary schemes. -/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Group.Kernel

universe u

attribute [local instance] Over.cartesianMonoidalCategory

example {S T : Scheme.{u}} (b : T ⟶ S) {G E : Grp (Over S)} (q : G ⟶ E) :
    (baseChangeIso b q).hom ≫ inclusion ((Over.pullback b).mapGrp.map q) =
      (Over.pullback b).mapGrp.map (inclusion q) :=
  baseChangeIso_hom_inclusion b q

/--
info: 'AlgebraicGeometry.Scheme.Group.Kernel.baseChangeIso_hom_inclusion' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms baseChangeIso_hom_inclusion
