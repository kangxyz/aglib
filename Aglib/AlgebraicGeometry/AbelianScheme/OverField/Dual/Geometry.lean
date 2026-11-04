/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Projectivity
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Isogeny
public import Aglib.AlgebraicGeometry.Cohomology.Group.H1

/-!
# Geometry of the original dual Picard component over every field

The general coherent-H1 bound applies to the original proper smooth
geometrically integral group. It discharges the H1 premises of the existing
dual criteria on the same supplied Picard representative. The resulting
component is proper and smooth of the source dimension; a projective source
gives projective geometrically integral dual geometry. The actual morphism
of an original ample bundle is finite, flat and surjective.

The locally Noetherian fppf representation, local finite type and
separatedness remain supplied. No different Picard model or existence of a
representative is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

variable {k : Type u} [Field k] (A : FScheme k) [GrpObj A]
  [Smooth A.hom] [GeometricallyIntegral A.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The original dual component is proper, smooth and of the source dimension
for the supplied representative and an actual ample bundle on the source. -/
theorem isProper_smooth_and_dimension_picardIdentityComponent
    [IsProper A.hom] (L : LineBundle A.left) (hL : L.IsAmple) :
    IsProper (picardIdentityComponent A.hom P R).hom ∧
      Smooth (picardIdentityComponent A.hom P R).hom ∧
      topologicalKrullDim (picardIdentityComponent A.hom P R).left =
        topologicalKrullDim A.left := by
  exact isProper_smooth_and_dimension_picardIdentityComponent_of_structureH1_le
    A P R L hL (Group.finrank_structureH1_le_finrank_identityCotangent A)

/-- An H-projective source gives an H-projective, smooth, geometrically
integral original dual component of the same dimension over every field. -/
theorem isHProjective_smooth_geometricallyIntegral_picardIdentityComponent
    [IsHProjective A.hom] :
    IsHProjective (picardIdentityComponent A.hom P R).hom ∧
      Smooth (picardIdentityComponent A.hom P R).hom ∧
      GeometricallyIntegral (picardIdentityComponent A.hom P R).hom ∧
      topologicalKrullDim (picardIdentityComponent A.hom P R).left =
        topologicalKrullDim A.left := by
  exact isHProjective_smooth_geometricallyIntegral_picardIdentityComponent_of_structureH1_le
    A P R (Group.finrank_structureH1_le_finrank_identityCotangent A)

/-- The actual original ample-line-bundle morphism to the supplied dual
component is finite, flat and surjective over every ground field. -/
theorem finite_flat_surjective_lineBundleClassMorphismIdentityComponent
    [IsProper A.hom] (L : LineBundle A.left) (hL : L.IsAmple) :
    IsFinite (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)).left ∧
      Flat (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)).left ∧
      Surjective (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)).left := by
  exact finite_flat_surjective_lineBundleClassMorphismIdentityComponent_of_structureH1_le
    A P R L hL (Group.finrank_structureH1_le_finrank_identityCotangent A)

end AlgebraicGeometry.Scheme.RelativePicard
