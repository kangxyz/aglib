/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Descent.IntrinsicCartier
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.OpenImmersion

/-!
# The original based theta divisor over the ground field

An actual rational origin gives the original translation to the whole
Picard scheme. The original based image is the pullback of the same
ground-field positive image along this open immersion. Its positive line
bundle is the dual of the original ideal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Abel.BoundedFamily

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  [IsSeparated P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- With the given rational origin, the original based theta image is
effective Cartier on the same Jacobian over the original field. -/
theorem isEffectiveCartier_basedAbelImage_groundField (hg : 0 < coherentGenus k X) :
    Hom.IsEffectiveCartier
      (jacobianAbelMorphism hX o ho P R (coherentGenus k X - 1)).left.imageι := by
  let := hX.smooth
  let := hX.proper
  let := picardCommGrpObj X.hom P R
  let n := coherentGenus k X - 1
  let t := GrpObj.mulRight (picardPoint P R
    (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))
  let : IsIso t.hom.left := by
    change IsIso ((Over.forget (Spec (.of k))).map t.hom)
    infer_instance
  let u := (identityComponentι P.obj).left ≫ t.hom.left
  let j : basedAbelImage hX o ho P R n ⟶ (identityComponentOver P.obj).left :=
    (jacobianAbelMorphism hX o ho P R n).left.imageι
  let a : positiveAbelImage X P R n ⟶ P.obj.left :=
    (positiveAbelMorphism X P R n).hom.left.imageι
  let e := basedAbelImageIsoPositive hX o ho P R n
  have he : e.hom ≫ a = j ≫ u := basedAbelImageIsoPositive_hom_comp hX o ho P R n
  have H : IsPullback e.hom j a u := IsPullback.of_horiz_isIso_mono ⟨he⟩
  have ha : Hom.IsEffectiveCartier a := isEffectiveCartier_positiveAbelImage_of_posGenus hX P R hg
  let m := Hom.idealPullbackMap a j u e.hom he
  have hm : IsIso m := Hom.idealPullbackMap_isIso_of_isOpenImmersion a j u e.hom he H
  exact ⟨inferInstance, isLocallyRankOne_of_iso _ (@asIso _ _ _ _ m hm)
    (pullback_locallyRankOne u _ ha.isLocallyRankOne)⟩

/-- The actual positive based theta line bundle over the original field. -/
def thetaLineBundleGroundField (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    LineBundle (identityComponentOver P.obj).left := by
  let := picardCommGrpObj X.hom P R
  exact dualLineBundle _
    (isEffectiveCartier_basedAbelImage_groundField hX o ho P R hg).idealLineBundle

/-- Over algebraically closed constants this is the same original bundle. -/
theorem thetaLineBundleGroundField_eq [IsAlgClosed k] (hg : 0 < coherentGenus k X) :
    thetaLineBundleGroundField hX o ho P R hg = thetaLineBundle hX o ho P R hg := rfl

/-- Translation by the given degree data pulls the original whole Picard
theta class back to the original based theta class on the Jacobian. -/
theorem pullbackClass_intrinsicThetaLineBundleOnPicard_translation
    (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    let n := coherentGenus k X - 1
    let t := GrpObj.mulRight (picardPoint P R
      (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))
    let u := (identityComponentι P.obj).left ≫ t.hom.left
    pullbackClass u (classOf P.obj.left (intrinsicThetaLineBundleOnPicard hX P R hg)) =
      classOf (identityComponentOver P.obj).left (thetaLineBundleGroundField hX o ho P R hg) := by
  let := hX.smooth
  let := hX.proper
  let := picardCommGrpObj X.hom P R
  let n := coherentGenus k X - 1
  let t := GrpObj.mulRight (picardPoint P R
    (n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)))
  let : IsIso t.hom.left := by
    change IsIso ((Over.forget (Spec (.of k))).map t.hom)
    infer_instance
  let u := (identityComponentι P.obj).left ≫ t.hom.left
  let i := (positiveAbelMorphism X P R n).hom.left.imageι
  let j := (jacobianAbelMorphism hX o ho P R n).left.imageι
  let e := basedAbelImageIsoPositive hX o ho P R n
  have w : e.hom ≫ i = j ≫ u := basedAbelImageIsoPositive_hom_comp hX o ho P R n
  have H : IsPullback e.hom j i u := IsPullback.of_horiz_isIso_mono ⟨w⟩
  have hm : IsIso (Hom.idealPullbackMap i j u e.hom w) :=
    Hom.idealPullbackMap_isIso_of_isOpenImmersion i j u e.hom w H
  exact Hom.pullbackClass_positiveCartier_of_isIso i j e.hom u w
    (isEffectiveCartier_positiveAbelImage_of_posGenus hX P R hg)
    (isEffectiveCartier_basedAbelImage_groundField hX o ho P R hg) hm

end AlgebraicGeometry.Scheme.OverField.Curve
