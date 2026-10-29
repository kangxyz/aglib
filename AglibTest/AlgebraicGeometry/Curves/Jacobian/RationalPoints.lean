/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.PicardScheme
public import Aglib.AlgebraicGeometry.Curves.Jacobian.RationalPoints

/-!
# Consumer checks for `Aglib.AlgebraicGeometry.Curves.Jacobian.RationalPoints`

Rational points of a representing scheme of the Picard sheaf of a curve with a rational point are
the line-bundle classes, as a group; axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

universe u

namespace AglibTest.CurvesJacobianRationalPoints

variable {k : Type u} [Field k] {X : FScheme k}

/-- With a rational point, the rational points of `P` are `Pic(X)`, bijectively. -/
example (hX : Curve.Properties X) (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
    (P : LocallyNoetherianOver (Spec (.of k))) (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) :
    Function.Bijective (picardPoint (X := X) P R) := by
  have := hX.proper
  have := hX.flat
  have := hX.isGeometricallyIntegral
  have : IsSplitEpi X.hom := IsSplitEpi.mk' ⟨o, ho⟩
  exact picardPoint_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral P R

/-- The group isomorphism `Pic(X) ≃+ Additive (Spec k ⟶ P)` sends `L` to its rational point. -/
example (hX : Curve.Properties X) (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
    (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom] (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
    (L : PicardGroup X.left) :
    haveI := hX.proper
    haveI := hX.flat
    haveI := hX.isGeometricallyIntegral
    haveI : IsSplitEpi X.hom := IsSplitEpi.mk' ⟨o, ho⟩
    letI := picardCommGrpObj X.hom P R
    Additive.toMul (picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral P R L) =
      picardPoint P R L := by
  have := hX.proper
  have := hX.flat
  have := hX.isGeometricallyIntegral
  have : IsSplitEpi X.hom := IsSplitEpi.mk' ⟨o, ho⟩
  exact picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_apply P R L

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.locallyNoetherianRationalPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.locallyNoetherianRationalPoint

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardPointClass' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.picardPointClass

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardPointClass_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.picardPointClass_apply

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardPointClass_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.picardPointClass_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardPointClassAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.picardPointClassAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.picardPoint

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.homEquiv_picardPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.homEquiv_picardPoint

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardPoint_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.picardPoint_eq_iff

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardPoint_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.picardPoint_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardPoint_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.picardPoint_zero

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_apply

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.parameterPoint_comp_abelMorphism_eq_picardPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.parameterPoint_comp_abelMorphism_eq_picardPoint

end AglibTest.CurvesJacobianRationalPoints

