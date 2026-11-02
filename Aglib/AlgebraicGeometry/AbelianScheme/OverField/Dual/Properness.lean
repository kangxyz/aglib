/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Dimension.QuasiFiniteSurjective
public import Aglib.AlgebraicGeometry.Group.Kernel.QuasiFinite
public import Aglib.AlgebraicGeometry.Morphisms.Proper.Over
public import Aglib.AlgebraicGeometry.Picard.IdentityComponent
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Dimension
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.LineBundle.AmpleKernel

/-!
# Properness criterion for the native dual Picard identity component

For the supplied locally Noetherian Picard representative `P,R`, an actual locally quasi-finite
group homomorphism from a proper group `A` to its Picard identity component is surjective if the
target unit-stalk dimension is at most the source unit-stalk dimension. Its image is closed
because the source is proper and the target separated; the native Picard identity component is
irreducible. The existing general local-dimension criterion gives surjectivity, and the existing
proper surjective-image theorem gives properness of this same target.

The locally quasi-finite map and the displayed local-dimension inequality are explicit
structural-criterion inputs. This result does not assert that an ample-line-bundle map or a
coherent-cohomology bound has already supplied them.

The final theorem uses the actual ample-line-bundle homomorphism and its proved finite
categorical kernel. It discharges local quasi-finiteness and leaves only the displayed original
coherent-H1 inequality explicit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] (A : FScheme k) [GrpObj A] [IsProper A.hom]
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- A locally quasi-finite native group homomorphism to the same Picard identity component is
surjective, and that component is proper, under the actual unit-stalk dimension inequality. -/
theorem surjective_and_isProper_picardIdentityComponent_of_unit_dimension_le
    (f : A ⟶ picardIdentityComponent A.hom P R) [IsMonHom f] [LocallyQuasiFinite f.left]
    (hdim : ringKrullDim ((picardIdentityComponent A.hom P R).left.presheaf.stalk
        (Group.unitPoint (picardIdentityComponent A.hom P R))) ≤
      ringKrullDim (A.left.presheaf.stalk (Group.unitPoint A))) :
    Surjective f.left ∧ IsProper (picardIdentityComponent A.hom P R).hom := by
  let := picardCommGrpObj A.hom P R
  let J := picardIdentityComponent A.hom P R
  have : IsSeparated J.hom := by
    change IsSeparated ((identityComponent P.obj).ι ≫ P.obj.hom)
    infer_instance
  have : LocallyOfFiniteType J.hom := by
    change LocallyOfFiniteType ((identityComponent P.obj).ι ≫ P.obj.hom)
    infer_instance
  have : IrreducibleSpace J.left := by
    change IrreducibleSpace (identityComponent P.obj).toScheme
    infer_instance
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have hpoint : f.left (Group.unitPoint A) = Group.unitPoint J := by
    have h := congrArg (fun a : 𝟙_ (FScheme k) ⟶ J =>
      a.left (IsLocalRing.closedPoint k)) (IsMonHom.one_hom f)
    change f.left ((MonObj.one (X := A)).left (IsLocalRing.closedPoint k)) =
      (MonObj.one (X := J)).left (IsLocalRing.closedPoint k)
    change f.left ((MonObj.one (X := A)).left (IsLocalRing.closedPoint k)) =
      (MonObj.one (X := J)).left (IsLocalRing.closedPoint k) at h
    exact h
  have : IsProper (f.left ≫ J.hom) := by
    rw [Over.w f]
    infer_instance
  have : IsProper f.left := IsProper.of_comp f.left J.hom
  have hclosed : IsClosed (Set.range f.left) := by
    simpa only [Set.image_univ] using f.left.isClosedMap Set.univ isClosed_univ
  have hs : Surjective f.left :=
    f.left.surjective_of_locallyQuasiFinite_of_isClosed_range_of_ringKrullDim_stalk_le_of_lt_top
      hclosed (Group.unitPoint A) (by rw [hpoint]; exact hdim) ringKrullDim_lt_top
  have : Surjective f.left := hs
  exact ⟨hs, Scheme.isProper_of_surjective_over_proper f⟩

/-- The actual ample-line-bundle homomorphism is surjective and the same chosen Picard identity
component is proper, assuming only the displayed original-H1 inequality beyond the geometric
source and representation hypotheses. Its finite kernel is supplied by the original ample map.
-/
theorem surjective_lineBundleClassMorphismIdentityComponent_and_isProper_of_structureH1_le
    [Smooth A.hom] [GeometricallyIntegral A.hom]
    (L : LineBundle A.left) (hL : L.IsAmple)
    (hH1 : Module.finrank k (structureCohomology k A 1) ≤
      Module.finrank k (Cotangent.Space η[A])) :
    Surjective (lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)).left ∧
      IsProper (picardIdentityComponent A.hom P R).hom := by
  let := picardCommGrpObj A.hom P R
  let φ := lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)
  let fg := lineBundleClassIdentityComponentGroupHom A P R (classOf A.left L)
  have : Flat A.hom := inferInstance
  have : IsFinite (Group.Kernel.group fg).X.hom :=
    isFinite_kernel_lineBundleClassIdentityComponentGroupHom A P R L hL
  have hf : LocallyQuasiFinite fg.hom.hom.left :=
    Group.Kernel.locallyQuasiFinite_of_isFinite_group fg
  have : LocallyQuasiFinite φ.left := hf
  have : IsMonHom φ := isMonHom_lineBundleClassMorphismIdentityComponent A P R (classOf A.left L)
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : PreconnectedSpace A.left := inferInstance
  have htarget :=
    (unit_dimension_cotangent_and_regular_picardIdentityComponent_of_structureH1_le
      A P R φ hH1).1
  have hsource := Group.ringKrullDim_unit_eq_finrank_identityCotangent_of_preconnected A
  exact surjective_and_isProper_picardIdentityComponent_of_unit_dimension_le A P R φ
    (htarget.le.trans hsource.ge)

end AlgebraicGeometry.Scheme.RelativePicard
