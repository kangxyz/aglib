/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# The additive sheaf of units of a commutative ring sheaf

Units are formed by the native right adjoint on commutative monoids. Their
additive spelling is the native equivalence between commutative and additive
commutative groups. Consequently units of an actual ring sheaf form an actual
abelian sheaf, with the original sectionwise unit maps.

The current consumer is the square-zero unit sequence for line-bundle lifting.
-/

@[expose] public section

open CategoryTheory

namespace CommRingCat

universe w

/-- The native group of units, written additively for sheaf cohomology. -/
def unitsAddFunctor : CommRingCat.{w} ⥤ AddCommGrpCat.{w} :=
  forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙ CommGrpCat.toAddCommGrp

instance : unitsAddFunctor.{w}.IsRightAdjoint := by
  change (forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
    commGroupAddCommGroupEquivalence.functor).IsRightAdjoint
  infer_instance

end CommRingCat

namespace CategoryTheory.Sheaf

universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Units of the original ring sections, as an actual abelian sheaf. -/
abbrev units (R : Sheaf J CommRingCat.{w}) : Sheaf J AddCommGrpCat.{w} :=
  (sheafCompose J CommRingCat.unitsAddFunctor).obj R

/-- The original map on units, with no sheafification or replacement. -/
abbrev unitsMap {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S) : R.units ⟶ S.units :=
  (sheafCompose J CommRingCat.unitsAddFunctor).map f

/-- The native additive sheaf underlying the same ring sections. -/
abbrev additive [UnivLE.{max u v, w}] (R : Sheaf J CommRingCat.{w}) :
    Sheaf J AddCommGrpCat.{w} :=
  (sheafCompose J (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj R

/-- Scalar forgetting applied to the original ring-sheaf map. -/
abbrev additiveMap [UnivLE.{max u v, w}] {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S) :
    R.additive ⟶ S.additive :=
  (sheafCompose J (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).map f

@[simp]
theorem unitsMap_apply {R S : Sheaf J CommRingCat.{w}} (f : R ⟶ S) (U : Cᵒᵖ)
    (x : R.units.obj.obj U) :
    ((unitsMap f).hom.app U x).toMul =
      Units.map ((f.hom.app U).hom : R.obj.obj U →* S.obj.obj U) x.toMul := rfl

@[simp]
theorem unitsMap_id (R : Sheaf J CommRingCat.{w}) : unitsMap (𝟙 R) = 𝟙 R.units := rfl

@[simp]
theorem unitsMap_comp {R S T : Sheaf J CommRingCat.{w}} (f : R ⟶ S) (g : S ⟶ T) :
    unitsMap (f ≫ g) = unitsMap f ≫ unitsMap g := rfl

end CategoryTheory.Sheaf
