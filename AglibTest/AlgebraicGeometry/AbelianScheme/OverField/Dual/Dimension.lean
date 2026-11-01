/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Dimension

/-!
# Consumer checks for the actual dual Picard unit-dimension criteria

The original coherent-H1 inequality remains explicit; target properness and smoothness are
not assumptions of the actual unit-stalk dimension and regularity conclusion.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Group
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AglibTest.FieldDualDimension

example {k : Type u} [Field k] (A : FScheme k) [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
    (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
    (f : A ⟶ picardIdentityComponent A.hom P R) [IsMonHom f] [LocallyQuasiFinite f.left]
    (hH1 : Module.finrank k (structureCohomology k A 1) ≤
      Module.finrank k (Cotangent.Space η[A])) :
    IsRegularLocalRing ((picardIdentityComponent A.hom P R).left.presheaf.stalk
      (Group.unitPoint (picardIdentityComponent A.hom P R))) :=
  (unit_dimension_cotangent_and_regular_picardIdentityComponent_of_structureH1_le
    A P R f hH1).2.2

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.identityComponentCotangent_le_of_structureH1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.identityComponentCotangent_le_of_structureH1_le

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.unit_dimension_cotangent_and_regular_picardIdentityComponent_of_structureH1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.unit_dimension_cotangent_and_regular_picardIdentityComponent_of_structureH1_le

end AglibTest.FieldDualDimension
