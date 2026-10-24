/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ObjectProperty.GrpObj

/-! Focused consumer of the transport of monoid, group and commutative group objects from a full
subcategory closed under finite products to the ambient cartesian monoidal category, with axiom
guards. -/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {P : ObjectProperty C}
  [P.IsClosedUnderLimitsOfShape (Discrete PEmpty)]
  [P.IsClosedUnderLimitsOfShape (Discrete WalkingPair)]

/-- The transported group object has the unit, multiplication and inverse of `X`. -/
example (X : P.FullSubcategory) [GrpObj X] :
    letI := GrpObj.ofFullSubcategory X
    MonObj.one (X := X.obj) = (MonObj.one (X := X)).hom ∧
      MonObj.mul (X := X.obj) = (MonObj.mul (X := X)).hom ∧
      GrpObj.inv (X := X.obj) = (GrpObj.inv (X := X)).hom :=
  ⟨rfl, rfl, rfl⟩

/-- A commutative group object of the full subcategory is commutative in `C`, for any braidings. -/
example [BraidedCategory C] [BraidedCategory P.FullSubcategory] (X : P.FullSubcategory)
    [CommGrpObj X] :
    letI := CommGrpObj.ofFullSubcategory X
    (β_ X.obj X.obj).hom ≫ MonObj.mul (X := X.obj) = MonObj.mul (X := X.obj) :=
  letI := CommGrpObj.ofFullSubcategory X
  IsCommMonObj.mul_comm X.obj

/-- The two braidings agree on underlying morphisms. -/
example [BraidedCategory C] [BraidedCategory P.FullSubcategory] (X Y : P.FullSubcategory) :
    (β_ X Y).hom.hom = (β_ X.obj Y.obj).hom :=
  ObjectProperty.braiding_hom_hom X Y

/--
info: 'CategoryTheory.CommGrpObj.ofFullSubcategory' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.CommGrpObj.ofFullSubcategory

/--
info: 'CategoryTheory.ObjectProperty.braiding_hom_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.ObjectProperty.braiding_hom_hom
