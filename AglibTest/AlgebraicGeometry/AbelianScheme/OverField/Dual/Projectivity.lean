/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Projectivity

/-! # Conditional projective dual geometry on the same original Picard component -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Group
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Cohomology

universe u

example {k : Type u} [Field k] (A : FScheme k) [GrpObj A]
    [IsHProjective A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
    (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
    [IsSeparated P.obj.hom]
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
    (hH1 : Module.finrank k (structureCohomology k A 1) ≤
      Module.finrank k (Cotangent.Space η[A])) :
    IsHProjective (picardIdentityComponent A.hom P R).hom ∧
      Smooth (picardIdentityComponent A.hom P R).hom ∧
      GeometricallyIntegral (picardIdentityComponent A.hom P R).hom ∧
      topologicalKrullDim (picardIdentityComponent A.hom P R).left =
        topologicalKrullDim A.left :=
  isHProjective_smooth_geometricallyIntegral_picardIdentityComponent_of_structureH1_le
    A P R hH1

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isHProjective_smooth_geometricallyIntegral_picardIdentityComponent_of_structureH1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.isHProjective_smooth_geometricallyIntegral_picardIdentityComponent_of_structureH1_le
