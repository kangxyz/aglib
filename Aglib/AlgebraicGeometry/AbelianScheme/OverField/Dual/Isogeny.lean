/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Smoothness
public import Aglib.AlgebraicGeometry.Geometrically.Reduced.Smooth
public import Aglib.AlgebraicGeometry.Group.Kernel.Finite
public import Aglib.AlgebraicGeometry.Group.Multiplication.FiniteFlat

/-!
# The actual ample-line-bundle map to the same Picard component

The original finite ample-map kernel and proper source make the same map
finite, without an H1 bound or target properness. Under the explicit original
coherent-H1 bound, the structural criterion gives surjectivity and smoothness
of the same target. Its native geometric irreducibility then gives geometric
integrality, and the general finite surjective group-homomorphism theorem
gives flatness over the original arbitrary field.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (A : FScheme k) [GrpObj A]
  [IsProper A.hom] [GeometricallyIntegral A.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The actual ample-line-bundle map to the original Picard identity component
is finite. Neither an H1 bound nor target properness is an input. -/
theorem isFinite_lineBundleClassMorphismIdentityComponent
    [Flat A.hom] (L : LineBundle A.left) (hL : L.IsAmple) :
    IsFinite (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)).left := by
  let := picardCommGrpObj A.hom P R
  let fg := lineBundleClassIdentityComponentGroupHom A P R (classOf A.left L)
  have : IsFinite (Group.Kernel.group fg).X.hom :=
    isFinite_kernel_lineBundleClassIdentityComponentGroupHom A P R L hL
  have : IsSeparated (picardIdentityComponent A.hom P R).hom := by
    change IsSeparated ((identityComponent P.obj).ι ≫ P.obj.hom)
    infer_instance
  exact Group.Kernel.isFinite_of_isFinite_group fg

/-- The actual ample-line-bundle map is finite, flat and surjective over every
field under the original coherent-H1 inequality. All target geometry is derived. -/
theorem finite_flat_surjective_lineBundleClassMorphismIdentityComponent_of_structureH1_le
    [Smooth A.hom] (L : LineBundle A.left) (hL : L.IsAmple)
    (hH1 : Module.finrank k (structureCohomology k A 1) ≤
      Module.finrank k (Cotangent.Space η[A])) :
    IsFinite (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)).left ∧
      Flat (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)).left ∧
      Surjective (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)).left := by
  let := picardCommGrpObj A.hom P R
  let J := picardIdentityComponent A.hom P R
  let φ := lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)
  let fg := lineBundleClassIdentityComponentGroupHom A P R (classOf A.left L)
  have : Flat A.hom := inferInstance
  have hfinite : IsFinite φ.left := isFinite_lineBundleClassMorphismIdentityComponent A P R L hL
  have hsurj : Surjective φ.left :=
    (surjective_lineBundleClassMorphismIdentityComponent_and_isProper_of_structureH1_le
      A P R L hL hH1).1
  have hsmooth : Smooth J.hom :=
    (isProper_smooth_and_dimension_picardIdentityComponent_of_structureH1_le
      A P R L hL hH1).2.1
  have : GeometricallyReduced J.hom := Scheme.geometricallyReduced_of_smooth _
  have : GeometricallyIntegral J.hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _
  have : IsFinite fg.hom.hom.left := hfinite
  have : Surjective fg.hom.hom.left := hsurj
  have hflat : Flat fg.hom.hom.left :=
    Group.finite_surjective_hom_flat (Grp.mk A) (Grp.mk J) fg
  exact ⟨hfinite, hflat, hsurj⟩

end AlgebraicGeometry.Scheme.RelativePicard
