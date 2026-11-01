/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Isogeny

/-! # The original ample map, with its unconditional finiteness boundary -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Group
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Cohomology

universe u

variable {k : Type u} [Field k] (A : FScheme k) [GrpObj A]
  [IsProper A.hom] [GeometricallyIntegral A.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

example [Flat A.hom] (L : LineBundle A.left) (hL : L.IsAmple) :
    IsFinite (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)).left :=
  isFinite_lineBundleClassMorphismIdentityComponent A P R L hL

example [Smooth A.hom] (L : LineBundle A.left) (hL : L.IsAmple)
    (hH1 : Module.finrank k (structureCohomology k A 1) ≤
      Module.finrank k (Cotangent.Space η[A])) :
    IsFinite (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)).left ∧
      Flat (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)).left ∧
      Surjective (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)).left :=
  finite_flat_surjective_lineBundleClassMorphismIdentityComponent_of_structureH1_le A P R L hL hH1

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isFinite_lineBundleClassMorphismIdentityComponent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.isFinite_lineBundleClassMorphismIdentityComponent

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.finite_flat_surjective_lineBundleClassMorphismIdentityComponent_of_structureH1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.finite_flat_surjective_lineBundleClassMorphismIdentityComponent_of_structureH1_le
