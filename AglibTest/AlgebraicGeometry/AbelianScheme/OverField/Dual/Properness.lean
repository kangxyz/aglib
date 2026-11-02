/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Properness

/-!
# Consumer checks for the actual-map Picard properness criterion

The source properness, locally quasi-finite map and actual unit-stalk inequality remain
explicit. The target's properness is a conclusion.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Group
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AglibTest.PicardAbelianVarietyProperness

example {k : Type u} [Field k] (A : FScheme k) [GrpObj A] [IsProper A.hom]
    (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
    [IsSeparated P.obj.hom]
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
    (f : A ⟶ picardIdentityComponent A.hom P R) [IsMonHom f] [LocallyQuasiFinite f.left]
    (hdim : ringKrullDim ((picardIdentityComponent A.hom P R).left.presheaf.stalk
        (Group.unitPoint (picardIdentityComponent A.hom P R))) ≤
      ringKrullDim (A.left.presheaf.stalk (Group.unitPoint A))) :
    Surjective f.left ∧ IsProper (picardIdentityComponent A.hom P R).hom :=
  surjective_and_isProper_picardIdentityComponent_of_unit_dimension_le A P R f hdim

example {k : Type u} [Field k] (A : FScheme k) [GrpObj A] [IsProper A.hom]
    [Smooth A.hom] [GeometricallyIntegral A.hom]
    (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
    [IsSeparated P.obj.hom]
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
    (L : LineBundle A.left) (hL : L.IsAmple)
    (hH1 : Module.finrank k (structureCohomology k A 1) ≤
      Module.finrank k (Cotangent.Space η[A])) :
    Surjective (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)).left ∧
      IsProper (picardIdentityComponent A.hom P R).hom :=
  surjective_lineBundleClassMorphismIdentityComponent_and_isProper_of_structureH1_le A P R L hL hH1

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.surjective_and_isProper_picardIdentityComponent_of_unit_dimension_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.surjective_and_isProper_picardIdentityComponent_of_unit_dimension_le

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.surjective_lineBundleClassMorphismIdentityComponent_and_isProper_of_structureH1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.surjective_lineBundleClassMorphismIdentityComponent_and_isProper_of_structureH1_le

end AglibTest.PicardAbelianVarietyProperness
