/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Nodal.Polygon.CoverPoints
public import Mathlib.Algebra.Field.ZMod

/-! Native clients of the actual polygon projection, including degree two in characteristic two. -/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AglibTest.PolygonFiniteCover

/-- Characteristic two is prime, so the test coefficient ring is a field. -/
local instance primeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩

example : IsFinite (Polygon.cycleMap (ZMod 2) 2) := inferInstance

example : Etale (Polygon.cycleMap (ZMod 2) 2) := inferInstance

example : Flat (Polygon.cycleMap (ZMod 2) 2) := Polygon.cycleMap_flat (ZMod 2) 2

example : Surjective (Polygon.cycleMap (ZMod 2) 2) :=
  Polygon.cycleMap_surjective (ZMod 2) 2

example (p : PinchedLine.pinchedGluing (ZMod 2)) :
    (Polygon.cycleMap (ZMod 2) 2).finrank p = 2 :=
  Polygon.cycleMap_finrank (ZMod 2) 2 p

example {T : Scheme} (g : T ⟶ PinchedLine.pinchedGluing (ZMod 2)) (t : T) :
    (pullback.snd (Polygon.cycleMap (ZMod 2) 2) g).finrank t = 2 :=
  Polygon.cycleMap_baseChange_finrank (ZMod 2) 2 g t

example (K : Type) [Field K] (p : Spec (.of K) ⟶ PinchedLine.pinchedGluing (ZMod 2)) :
    Polygon.fieldPointLift (ZMod 2) 2 K p ≫ Polygon.cycleMap (ZMod 2) 2 = p :=
  Polygon.fieldPointLift_map (ZMod 2) 2 K p

example (K : Type) [Field K] (p : Spec (.of K) ⟶ PinchedLine.pinchedGluing (ZMod 2)) :
    Polygon.fieldPointLift (ZMod 2) 2 K p ≫ Polygon.structureMap (ZMod 2) 2 =
      p ≫ PinchedLine.pinchedStructure (ZMod 2) :=
  Polygon.fieldPointLift_over (ZMod 2) 2 K p

example : (Polygon.finiteEtaleCycleCover (ZMod 2) 2).obj.hom =
    Polygon.cycleMap (ZMod 2) 2 := rfl

example : (Polygon.cycleMorphism (ZMod 2) 2).left = Polygon.cycleMap (ZMod 2) 2 := rfl

example : IsFinite (Polygon.cycleMap (ZMod 2) 0) := inferInstance

example : Etale (Polygon.cycleMap (ZMod 2) 0) := inferInstance

example (p : PinchedLine.pinchedGluing (ZMod 2)) :
    (Polygon.cycleMap (ZMod 2) 0).finrank p = 0 :=
  Polygon.cycleMap_finrank (ZMod 2) 0 p

end AglibTest.PolygonFiniteCover
