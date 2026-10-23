/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.ClosedSubscheme

/-! Focused consumer of relative flatness of the structure module and the ideal module of a
closed subscheme, with axiom guards. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- Flatness of a closed subscheme is relative flatness of its structure module. -/
example {X S : Scheme.{u}} (p : X ⟶ S) (W : X.IdealSheafData) :
    Scheme.Modules.relativeFlat p W.quotientModule ↔ Flat (W.subschemeι ≫ p) :=
  W.relativeFlat_quotientModule_iff_flat p

/-- `f^* 𝒪_W` is flat over `S` exactly when `W.comap f` is, with no flatness of `W`. -/
example {X Y S : Scheme.{u}} (p : Y ⟶ S) (W : X.IdealSheafData) (f : Y ⟶ X) :
    Scheme.Modules.relativeFlat p ((Scheme.Modules.pullback f).obj W.quotientModule) ↔
      Flat ((W.comap f).subschemeι ≫ p) :=
  W.relativeFlat_pullback_quotientModule_iff p f

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_pushforward_unit_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_pushforward_unit_of_flat

/--
info: 'AlgebraicGeometry.Scheme.Modules.flat_comp_of_relativeFlat_pushforward_unit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.flat_comp_of_relativeFlat_pushforward_unit

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.relativeFlat_quotientModule_iff_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.relativeFlat_quotientModule_iff_flat

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.relativeFlat_pullback_quotientModule_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.relativeFlat_pullback_quotientModule_iff

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_idealModule_of_flat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_idealModule_of_flat
