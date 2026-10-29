/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.AbelMorphism

/-!
# Consumer checks for `Aglib.AlgebraicGeometry.Curves.Jacobian.AbelMorphism`

The Abel morphism `X^n ⟶ P` for a representation `R`, its value on tuples, the origin, its closed
image inside the identity component; axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

universe u

namespace AglibTest.CurvesJacobianAbelMorphism

variable {k : Type u} [Field k] {X : FScheme k}

/-- The Abel morphism is the morphism of locally Noetherian `k`-schemes attached to the class of
the graph-sum family. -/
example [SmoothOfRelativeDimension 1 X.hom] [IsProper X.hom] (o : Spec (.of k) ⟶ X.left)
    (ho : o ≫ X.hom = 𝟙 _) (P : LocallyNoetherianOver (Spec (.of k))) (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) (n : ℕ) :
    R.homEquiv (abelMorphism o ho P R n) = abelSection X o ho n :=
  homEquiv_abelMorphism o ho P R n

/-- The image of the Abel morphism is closed and lies in the identity component. -/
example (hX : Curve.Properties X) (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
    (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
    [IsSeparated P.obj.hom] (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P) (n : ℕ) :
    letI := hX.smooth
    letI := hX.proper
    letI := picardCommGrpObj X.hom P R
    IsClosed (Set.range (abelMorphism o ho P R n).hom.left) ∧
      Set.range (abelMorphism o ho P R n).hom.left ⊆ identityComponent P.obj := by
  let := hX.smooth
  let := hX.proper
  exact ⟨isClosed_range_abelMorphism o ho P R n,
    range_abelMorphism_subset_identityComponent o ho P R hX n⟩

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.connectedSpace_finiteProductOver' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.connectedSpace_finiteProductOver

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.connectedSpace_parameter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.connectedSpace_parameter

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.familyScheme_map_eq_familyMap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.familyScheme_map_eq_familyMap

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.locallyNoetherianParameter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.locallyNoetherianParameter

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.abelSection' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.abelSection

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.abelMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.abelMorphism

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.homEquiv_abelMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.homEquiv_abelMorphism

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.homEquiv_comp_abelMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.homEquiv_comp_abelMorphism

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.homEquiv_parameterPoint_comp_abelMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.homEquiv_parameterPoint_comp_abelMorphism

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.originPoint' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.originPoint

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.abelClass_eq_zero_of_eq_comp_origin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.abelClass_eq_zero_of_eq_comp_origin

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.isProper_abelMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.isProper_abelMorphism

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.isClosed_range_abelMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.isClosed_range_abelMorphism

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.originPoint_comp_abelMorphism' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.originPoint_comp_abelMorphism

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.range_abelMorphism_subset_identityComponent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily.range_abelMorphism_subset_identityComponent

end AglibTest.CurvesJacobianAbelMorphism

