/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Smoothness
public import Aglib.AlgebraicGeometry.Geometrically.Reduced.Smooth
public import Aglib.AlgebraicGeometry.Picard.Scheme.IdentityComponentProjectiveSource
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Ample

/-!
# Projectivity and geometric integrality of the same dual Picard component

The original projective source supplies an ample bundle internally. The explicit
original-H1 bound then gives properness, smoothness and dimension of the same
supplied Picard identity component. Its native geometric irreducibility and
smoothness give geometric integrality. General Picard quasi-projectivity together
with this properness gives H-projectivity over the original arbitrary field.

The coherent-H1 inequality remains explicit until its native supplier is proved.
No target geometry, curve condition or new Picard representative is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

variable {k : Type u} [Field k] (A : FScheme k) [GrpObj A]
  [IsHProjective A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The same chosen Picard component is H-projective, smooth, geometrically
integral and of the source dimension, under the original coherent-H1 bound. -/
theorem isHProjective_smooth_geometricallyIntegral_picardIdentityComponent_of_structureH1_le
    (hH1 : Module.finrank k (structureCohomology k A 1) ≤
      Module.finrank k (Cotangent.Space η[A])) :
    IsHProjective (picardIdentityComponent A.hom P R).hom ∧
      Smooth (picardIdentityComponent A.hom P R).hom ∧
      GeometricallyIntegral (picardIdentityComponent A.hom P R).hom ∧
      topologicalKrullDim (picardIdentityComponent A.hom P R).left =
        topologicalKrullDim A.left := by
  obtain ⟨L, hL⟩ := IsHProjective.exists_isAmple A.hom
  obtain ⟨hproper, hsmooth, hdim⟩ :=
    isProper_smooth_and_dimension_picardIdentityComponent_of_structureH1_le A P R L hL hH1
  have : Flat A.hom := inferInstance
  have : IsHQuasiProjective (picardIdentityComponent A.hom P R).hom :=
    isHQuasiProjective_picardIdentityComponent_of_isHProjective A P R
  have hprojective : IsHProjective (picardIdentityComponent A.hom P R).hom :=
    IsHProjective.of_isHQuasiProjective_of_isProper _
  have : GeometricallyReduced (picardIdentityComponent A.hom P R).hom :=
    Scheme.geometricallyReduced_of_smooth _
  have hintegral : GeometricallyIntegral (picardIdentityComponent A.hom P R).hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _
  exact ⟨hprojective, hsmooth, hintegral, hdim⟩

end AlgebraicGeometry.Scheme.RelativePicard
