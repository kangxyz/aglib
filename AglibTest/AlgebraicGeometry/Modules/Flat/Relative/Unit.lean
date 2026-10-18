/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Unit

/-! Focused consumer of the flatness of the structure module, with axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/-- The structure module is relatively flat over a flat morphism, and its stalks are flat. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (x : X) :
    Scheme.Modules.relativeFlat f (SheafOfModules.unit X.ringCatSheaf) ∧
      Module.Flat (X.presheaf.stalk x)
        ((Scheme.Modules.moduleStalk X x).obj (SheafOfModules.unit X.ringCatSheaf)) :=
  ⟨Scheme.Modules.relativeFlat_unit_of_flat f, inferInstance⟩

/--
info: 'AlgebraicGeometry.Scheme.Modules.unit_stalk_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.unit_stalk_flat

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_unit_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_unit_of_flat
