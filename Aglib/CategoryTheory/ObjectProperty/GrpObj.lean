/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# Group objects of a full subcategory closed under finite products

Let `C` be a cartesian monoidal category and `P` a property of objects of `C` closed under the
terminal object and binary products. Mathlib's `CartesianMonoidalCategory.fullSubcategory` makes
`P.FullSubcategory` cartesian monoidal with the products of `C`: the tensor product of `X` and `Y`
has underlying object `X.obj ⊗ Y.obj`, and the unit, unitors, associators, projections, lifts and
maps to the unit are those of `C`, all by definition. The inclusion `P.ι` preserves this
structure on the nose; no `Functor.Monoidal` instance is used.

Hence a monoid, group or commutative monoid object `X` of `P.FullSubcategory` is the same
structure on `X.obj` in `C`, with the same unit `η[X].hom`, multiplication `μ[X].hom` and inverse
`(GrpObj.inv (X := X)).hom`: `MonObj.ofFullSubcategory`, `GrpObj.ofFullSubcategory`,
`IsCommMonObj.ofFullSubcategory` and `CommGrpObj.ofFullSubcategory`. Each axiom is the image under
the inclusion of the corresponding axiom in `P.FullSubcategory`. The braidings of `C` and of
`P.FullSubcategory` are arbitrary: in a cartesian monoidal category every braiding exchanges the
two projections (Mathlib's `braiding_hom_fst`, `braiding_hom_snd`), so the two braidings agree
(`ObjectProperty.braiding_hom_hom`).

These constructions are definitions, not instances, since `X.obj` may carry another structure.
The consumer is the group law of a scheme locally of finite type over a locally Noetherian base
that represents a presheaf of abelian groups on locally Noetherian test schemes
(`Aglib.AlgebraicGeometry.Sites.OverRepresentability.CommGrpObj`): the products of the
representing scheme with itself are formed in the full subcategory of schemes locally of finite
type over the base.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits MonoidalCategory CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {P : ObjectProperty C}
  [P.IsClosedUnderLimitsOfShape (Discrete PEmpty)]
  [P.IsClosedUnderLimitsOfShape (Discrete WalkingPair)]

/-- The braidings of `P.FullSubcategory` and of `C` agree on underlying morphisms: both exchange
the two projections. -/
theorem ObjectProperty.braiding_hom_hom [BraidedCategory C] [BraidedCategory P.FullSubcategory]
    (X Y : P.FullSubcategory) : (β_ X Y).hom.hom = (β_ X.obj Y.obj).hom := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [braiding_hom_fst]
    exact congrArg InducedCategory.Hom.hom (braiding_hom_fst X Y)
  · rw [braiding_hom_snd]
    exact congrArg InducedCategory.Hom.hom (braiding_hom_snd X Y)

/-- **A monoid object of a full subcategory closed under finite products is a monoid object of
the ambient category**, with unit `η[X].hom` and multiplication `μ[X].hom`. -/
@[instance_reducible]
def MonObj.ofFullSubcategory (X : P.FullSubcategory) [MonObj X] : MonObj X.obj where
  one := (MonObj.one (X := X)).hom
  mul := (MonObj.mul (X := X)).hom
  one_mul := congrArg InducedCategory.Hom.hom (MonObj.one_mul X)
  mul_one := congrArg InducedCategory.Hom.hom (MonObj.mul_one X)
  mul_assoc := congrArg InducedCategory.Hom.hom (MonObj.mul_assoc X)

theorem MonObj.ofFullSubcategory_one (X : P.FullSubcategory) [MonObj X] :
    (MonObj.ofFullSubcategory X).one = (MonObj.one (X := X)).hom :=
  rfl

theorem MonObj.ofFullSubcategory_mul (X : P.FullSubcategory) [MonObj X] :
    (MonObj.ofFullSubcategory X).mul = (MonObj.mul (X := X)).hom :=
  rfl

/-- **A group object of a full subcategory closed under finite products is a group object of the
ambient category**, with the unit, multiplication and inverse of `X`. -/
@[instance_reducible]
def GrpObj.ofFullSubcategory (X : P.FullSubcategory) [GrpObj X] : GrpObj X.obj where
  __ := MonObj.ofFullSubcategory X
  inv := (GrpObj.inv (X := X)).hom
  left_inv := congrArg InducedCategory.Hom.hom (GrpObj.left_inv X)
  right_inv := congrArg InducedCategory.Hom.hom (GrpObj.right_inv X)

theorem GrpObj.ofFullSubcategory_inv (X : P.FullSubcategory) [GrpObj X] :
    (GrpObj.ofFullSubcategory X).inv = (GrpObj.inv (X := X)).hom :=
  rfl

/-- **A commutative monoid object of a full subcategory closed under finite products is
commutative in the ambient category.** -/
theorem IsCommMonObj.ofFullSubcategory [BraidedCategory C] [BraidedCategory P.FullSubcategory]
    (X : P.FullSubcategory) [MonObj X] [IsCommMonObj X] :
    letI := MonObj.ofFullSubcategory X
    IsCommMonObj X.obj := by
  let := MonObj.ofFullSubcategory X
  constructor
  rw [← ObjectProperty.braiding_hom_hom X X]
  exact congrArg InducedCategory.Hom.hom (IsCommMonObj.mul_comm X)

/-- **A commutative group object of a full subcategory closed under finite products is a
commutative group object of the ambient category**, with the unit, multiplication and inverse of
`X`. -/
@[instance_reducible]
def CommGrpObj.ofFullSubcategory [BraidedCategory C] [BraidedCategory P.FullSubcategory]
    (X : P.FullSubcategory) [CommGrpObj X] : CommGrpObj X.obj where
  __ := GrpObj.ofFullSubcategory X
  __ := IsCommMonObj.ofFullSubcategory X

end CategoryTheory
