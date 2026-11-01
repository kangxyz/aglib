/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.Cartier
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.EvaluationFamily
public import Aglib.AlgebraicGeometry.Curves.Jacobian.AbelCurve
public import Aglib.AlgebraicGeometry.Group.Translation.Incidence
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.FlatMorphism

/-!
# The actual theta incidence on the canonical curve family

Use the existing based Abel image with its original inclusion in the same
Jacobian. The canonical group translation isomorphism supplies incidence,
and the original parameter-open inclusion restricts it to X times V.
The resulting closed immersion is the actual pullback of theta along
(a,q) mapped to a-f(q), on all scheme tests.

The ambient difference map is smooth: it is an open restriction of a
translation isomorphism followed by the base change of the smooth curve.
Consequently the original theta ideal pulls back as an effective Cartier
ideal. Independently, the incidence source is an open subscheme of the
original product of theta with X, and is reduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Opposite AlgebraicGeometry Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Abel.BoundedFamily

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

/-- The existing based image with its original structural map. -/
def thetaImageOver : FScheme k := by
  let := picardCommGrpObj X.hom P R
  exact Over.mk ((jacobianAbelMorphism hX o ho P R (coherentGenus k X - 1)).left.imageι ≫
    (identityComponentOver P.obj).hom)

/-- The original image inclusion, regarded over the original field. -/
def thetaImageInclusion :
    letI := picardCommGrpObj X.hom P R
    thetaImageOver hX o ho P R ⟶ identityComponentOver P.obj := by
  let := picardCommGrpObj X.hom P R
  exact Over.homMk (jacobianAbelMorphism hX o ho P R (coherentGenus k X - 1)).left.imageι rfl

/-- Restrict the original J-times-X ambient scheme to the same X-times-V
using the native braiding and original parameter inclusion. -/
def thetaIncidenceRestrictionMap :
    letI := picardCommGrpObj X.hom P R
    X ⊗ thetaParameterOver hX o ho P R ⟶ identityComponentOver P.obj ⊗ X := by
  let := picardCommGrpObj X.hom P R
  exact (β_ X (thetaParameterOver hX o ho P R)).hom ≫
    (thetaParameterι hX o ho P R ⊗ₘ 𝟙 X)

/-- The original whole translated image map, before restricting or
passing to any field-valued point. -/
def thetaIncidenceMorphism :
    letI := picardCommGrpObj X.hom P R
    thetaImageOver hX o ho P R ⊗ X ⟶ identityComponentOver P.obj ⊗ X := by
  let := picardCommGrpObj X.hom P R
  exact incidenceMorphism (identityComponentOver P.obj) (thetaImageInclusion hX o ho P R)
    (jacobianCurveMorphism hX o ho P R)

/-- The literal closed immersion on the canonical family X times V. -/
def thetaIncidenceInclusion :
    pullback (thetaIncidenceMorphism hX o ho P R).left
      (thetaIncidenceRestrictionMap hX o ho P R).left ⟶
        pullback X.hom (thetaParameterOver hX o ho P R).hom :=
  pullback.snd _ _

/-- The whole ambient difference map, from the SAME canonical shear. -/
def thetaIncidenceDifference :
    letI := picardCommGrpObj X.hom P R
    X ⊗ thetaParameterOver hX o ho P R ⟶ identityComponentOver P.obj := by
  let := picardCommGrpObj X.hom P R
  exact thetaIncidenceRestrictionMap hX o ho P R ≫
    incidenceDifference (identityComponentOver P.obj) (jacobianCurveMorphism hX o ho P R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ambient restriction is an open immersion of the original schemes. -/
theorem isOpenImmersion_thetaIncidenceRestrictionMap :
    IsOpenImmersion (thetaIncidenceRestrictionMap hX o ho P R).left := by
  let := picardCommGrpObj X.hom P R
  have : IsOpenImmersion (thetaParameterι hX o ho P R).left :=
    inferInstanceAs (IsOpenImmersion (rankOneNonRepeatedOpen hX o ho P R).ι)
  simp only [thetaIncidenceRestrictionMap, Over.comp_left, Over.braiding_hom_left,
    Over.tensorHom_left]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The literal restricted incidence is the actual pullback of the
original theta immersion along the whole original difference map. -/
theorem isPullback_thetaIncidence :
    letI := picardCommGrpObj X.hom P R
    IsPullback
      (pullback.fst (thetaIncidenceMorphism hX o ho P R).left
        (thetaIncidenceRestrictionMap hX o ho P R).left ≫
          (fst (thetaImageOver hX o ho P R) X).left)
      (thetaIncidenceInclusion hX o ho P R)
      (thetaImageInclusion hX o ho P R).left (thetaIncidenceDifference hX o ho P R).left := by
  let := picardCommGrpObj X.hom P R
  exact (IsPullback.of_hasPullback _ _).paste_horiz
    (isPullback_incidenceMorphism (identityComponentOver P.obj)
      (thetaImageInclusion hX o ho P R) (jacobianCurveMorphism hX o ho P R))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restricted incidence is a closed immersion of the canonical family. -/
theorem isClosedImmersion_thetaIncidenceInclusion :
    IsClosedImmersion (thetaIncidenceInclusion hX o ho P R) := by
  let := picardCommGrpObj X.hom P R
  have : IsClosedImmersion (thetaImageInclusion hX o ho P R).left :=
    inferInstanceAs (IsClosedImmersion
      (jacobianAbelMorphism hX o ho P R (coherentGenus k X - 1)).left.imageι)
  exact MorphismProperty.of_isPullback (isPullback_thetaIncidence hX o ho P R) inferInstance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual ambient difference map is smooth, even when the Abel
curve morphism itself is not flat. -/
theorem smooth_thetaIncidenceDifference : Smooth (thetaIncidenceDifference hX o ho P R).left := by
  let := picardCommGrpObj X.hom P R
  have := hX.smooth
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : Smooth (fst (identityComponentOver P.obj) X).left :=
    inferInstanceAs (Smooth (pullback.fst (identityComponentOver P.obj).hom X.hom))
  have := isOpenImmersion_thetaIncidenceRestrictionMap hX o ho P R
  change Smooth ((thetaIncidenceRestrictionMap hX o ho P R).left ≫
    (GrpObj.translationFamily (identityComponentOver P.obj)
      (jacobianCurveMorphism hX o ho P R)).inv.left ≫
        (fst (identityComponentOver P.obj) X).left)
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original incidence source is reduced as an open subscheme of
the original product theta times X. This includes an empty restriction. -/
theorem isReduced_thetaIncidence :
    IsReduced (pullback (thetaIncidenceMorphism hX o ho P R).left
      (thetaIncidenceRestrictionMap hX o ho P R).left) := by
  let := picardCommGrpObj X.hom P R
  have := hX.smooth
  have := hX.flat
  have := hX.isGeometricallyIntegral
  have : IsIntegral (thetaImageOver hX o ho P R).left :=
    isIntegral_basedAbelImage hX o ho P R (coherentGenus k X - 1)
  have : LocallyOfFiniteType (thetaImageOver hX o ho P R).hom := by
    change LocallyOfFiniteType
      ((jacobianAbelMorphism hX o ho P R (coherentGenus k X - 1)).left.imageι ≫
        (identityComponentOver P.obj).hom)
    infer_instance
  have : IsLocallyNoetherian (thetaImageOver hX o ho P R).left :=
    LocallyOfFiniteType.isLocallyNoetherian (thetaImageOver hX o ho P R).hom
  have : IsReduced (thetaImageOver hX o ho P R ⊗ X).left :=
    inferInstanceAs (IsReduced (pullback (thetaImageOver hX o ho P R).hom X.hom))
  have := isOpenImmersion_thetaIncidenceRestrictionMap hX o ho P R
  exact isReduced_of_isOpenImmersion (pullback.fst
    (thetaIncidenceMorphism hX o ho P R).left (thetaIncidenceRestrictionMap hX o ho P R).left)

variable [IsAlgClosed k]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original theta Cartier ideal pulls back along the smooth ambient
difference map to the actual restricted incidence ideal. -/
theorem isEffectiveCartier_thetaIncidence (hg : 0 < coherentGenus k X) :
    Hom.IsEffectiveCartier (thetaIncidenceInclusion hX o ho P R) := by
  let := picardCommGrpObj X.hom P R
  let H := isPullback_thetaIncidence hX o ho P R
  let hTheta := isEffectiveCartier_basedAbelImage_pred hX o ho P R hg
  have : IsClosedImmersion (thetaImageInclusion hX o ho P R).left := hTheta.isClosedImmersion
  have := smooth_thetaIncidenceDifference hX o ho P R
  have := Hom.idealPullbackMap_isIso_of_flat (thetaImageInclusion hX o ho P R).left
    (thetaIncidenceDifference hX o ho P R).left (thetaIncidenceInclusion hX o ho P R)
    _ H.w H
  exact ⟨isClosedImmersion_thetaIncidenceInclusion hX o ho P R,
    isLocallyRankOne_of_iso _ (asIso (Hom.idealPullbackMap _ _ _ _ H.w))
      (pullback_locallyRankOne _ _ hTheta.isLocallyRankOne)⟩

end AlgebraicGeometry.Scheme.OverField.Curve
