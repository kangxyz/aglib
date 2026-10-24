/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.IdealSheaf.ImageOverBase

/-! Focused consumer of the comparison of a closed subscheme with its image over a base: the same
image in the base and the same properties over it, with axiom guards. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/-- A closed subscheme closed in `Y` and its image in `Y` have the same image in `T` and are proper
over `T` together. -/
example {X Y T : Scheme.{u}} (I : X.IdealSheafData) (j : X ⟶ Y) (q : Y ⟶ T)
    [IsClosedImmersion (I.subschemeι ≫ j)] :
    Set.range ((I.map j).subschemeι ≫ q) = Set.range (I.subschemeι ≫ j ≫ q) ∧
      (IsProper ((I.map j).subschemeι ≫ q) ↔ IsProper (I.subschemeι ≫ j ≫ q)) :=
  ⟨I.range_map_subschemeι_comp rfl, I.map_subschemeι_comp_iff rfl @IsProper⟩

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.range_map_subschemeι_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.range_map_subschemeι_comp

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.map_subschemeι_comp_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.map_subschemeι_comp_iff
