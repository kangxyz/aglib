/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.IdealSheaf.QuotientModule.Map

/-! Focused consumer of the structure module of the image of a closed subscheme:
`j_* 𝒪_V ≅ 𝒪_{V.map j}` for a closed subscheme `V` closed in the target, in particular for every
closed subscheme along a closed immersion, with an axiom guard. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

/-- A closed subscheme `V ⊆ X` closed in `Y` has `j_* 𝒪_V ≅ 𝒪_{V.map j}`. -/
example {X Y : Scheme.{u}} (j : X ⟶ Y) (V : X.IdealSheafData)
    [IsClosedImmersion (V.subschemeι ≫ j)] :
    (Scheme.Modules.pushforward j).obj V.quotientModule ≅ (V.map j).quotientModule :=
  V.quotientModulePushforwardIso j

/-- Along a closed immersion every closed subscheme is closed in the target. -/
example {X Y : Scheme.{u}} (j : X ⟶ Y) [IsClosedImmersion j] (V : X.IdealSheafData) :
    (Scheme.Modules.pushforward j).obj V.quotientModule ≅ (V.map j).quotientModule :=
  V.quotientModulePushforwardIso j

/--
info: 'AlgebraicGeometry.Scheme.IdealSheafData.quotientModulePushforwardIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Scheme.IdealSheafData.quotientModulePushforwardIso
