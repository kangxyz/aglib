/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Invertible.ChartCocycle

/-! Focused consumer of the chart-cocycle reconstruction: every actual line bundle is
isomorphic to the glued line bundle of a unit cocycle indexed by the points, and the
actual Picard group of a scheme in `Scheme.{u}` is `u`-small, with no hypothesis on
the scheme. -/

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules.Invertible

universe u

example (X : Scheme.{u}) : Small.{u} (PicardGroup X) := inferInstance

example {X : Scheme.{u}} (L : LineBundle X) : (chartCocycle L).sheaf ≅ L.val :=
  chartReconstructionIso L

example {X : Scheme.{u}} (a : PicardGroup X) :
    ∃ (U : X → X.Opens) (c : UnitCocycle U) (hU : iSup U = ⊤),
      classOf X (c.lineBundle hU) = a :=
  exists_unitCocycle_classOf a

/-- A `Type u` model of the Picard group exists through `Shrink`. -/
example (X : Scheme.{u}) : Type u := Shrink.{u} (PicardGroup X)

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.small_picardGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms small_picardGroup
