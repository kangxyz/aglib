/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Geometry

/-! # Original dual geometry without a supplied coherent-H1 bound -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.Modules.Invertible

universe u

variable {k : Type u} [Field k] (A : FScheme k) [GrpObj A]
  [Smooth A.hom] [GeometricallyIntegral A.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

example [IsProper A.hom] (L : LineBundle A.left) (hL : L.IsAmple) :
    IsProper (picardIdentityComponent A.hom P R).hom ∧
      Smooth (picardIdentityComponent A.hom P R).hom ∧
      topologicalKrullDim (picardIdentityComponent A.hom P R).left =
        topologicalKrullDim A.left :=
  isProper_smooth_and_dimension_picardIdentityComponent A P R L hL

example [IsHProjective A.hom] :
    IsHProjective (picardIdentityComponent A.hom P R).hom ∧
      Smooth (picardIdentityComponent A.hom P R).hom ∧
      GeometricallyIntegral (picardIdentityComponent A.hom P R).hom ∧
      topologicalKrullDim (picardIdentityComponent A.hom P R).left =
        topologicalKrullDim A.left :=
  isHProjective_smooth_geometricallyIntegral_picardIdentityComponent A P R

example [IsProper A.hom] (L : LineBundle A.left) (hL : L.IsAmple) :
    IsFinite (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)).left ∧
      Flat (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)).left ∧
      Surjective (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)).left :=
  finite_flat_surjective_lineBundleClassMorphismIdentityComponent A P R L hL

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isProper_smooth_and_dimension_picardIdentityComponent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isProper_smooth_and_dimension_picardIdentityComponent

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isHProjective_smooth_geometricallyIntegral_picardIdentityComponent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isHProjective_smooth_geometricallyIntegral_picardIdentityComponent

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.finite_flat_surjective_lineBundleClassMorphismIdentityComponent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms finite_flat_surjective_lineBundleClassMorphismIdentityComponent
