/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Monoidal.GrpObjShear

/-!
# The shear automorphism of a group object

The examples restate that the shear automorphism of a group object in a cartesian monoidal
category is followed by the projections as the division map and the second projection, that its
inverse is the multiplication shear, and guard the axioms.
-/

@[expose] public section

namespace AglibTest.GrpObjShear

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] (G : C) [GrpObj G]

/-- The shear followed by the first projection is the division map. -/
theorem fst_comp : (GrpObj.shearIso G).hom ≫ fst G G = fst G G / snd G G :=
  GrpObj.shearIso_hom_fst G

/-- The inverse of the shear is `(c, b) ↦ (c b, b)`. -/
example : (GrpObj.shearIso G).inv = lift (fst G G * snd G G) (snd G G) := rfl

/-- The shear is an automorphism. -/
example : (GrpObj.shearIso G).hom ≫ (GrpObj.shearIso G).inv = 𝟙 _ := Iso.hom_inv_id _

/-- info: 'CategoryTheory.GrpObj.shearIso' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GrpObj.shearIso

/-- info: 'AglibTest.GrpObjShear.fst_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fst_comp

end AglibTest.GrpObjShear
