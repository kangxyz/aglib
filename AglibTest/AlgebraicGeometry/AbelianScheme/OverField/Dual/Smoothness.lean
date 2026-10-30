/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Smoothness

/-!
# Consumer checks for same-P/R dual Picard geometry under the original H1 bound

The original coherent-H1 inequality and an actual ample line bundle are explicit. Finite
kernel, local quasi-finiteness, field-extension rank transport and fpqc descent are supplied by
the implementation, with no target geometry as an input.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Group
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AglibTest.FieldDualSmoothness

example {k : Type u} [Field k] (A : FScheme k) [GrpObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
    (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
    [IsSeparated P.obj.hom]
    (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
    (L : LineBundle A.left) (hL : L.IsAmple)
    (hH1 : Module.finrank k (structureCohomology k A 1) ≤
      Module.finrank k (Cotangent.Space η[A])) :
    IsProper (picardIdentityComponent A.hom P R).hom ∧
      Smooth (picardIdentityComponent A.hom P R).hom ∧
      topologicalKrullDim (picardIdentityComponent A.hom P R).left =
        topologicalKrullDim A.left :=
  isProper_smooth_and_dimension_picardIdentityComponent_of_structureH1_le A P R L hL hH1

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.smooth_and_dimension_picardIdentityComponent_of_structureH1_le_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.smooth_and_dimension_picardIdentityComponent_of_structureH1_le_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isProper_smooth_and_dimension_picardIdentityComponent_of_structureH1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.RelativePicard.isProper_smooth_and_dimension_picardIdentityComponent_of_structureH1_le

end AglibTest.FieldDualSmoothness
