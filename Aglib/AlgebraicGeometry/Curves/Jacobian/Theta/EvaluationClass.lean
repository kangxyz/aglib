/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.EvaluationFamily
public import Aglib.AlgebraicGeometry.Picard.Strata.Relation.Basic

/-!
# Whole classifying map of the actual evaluation divisor

The original evaluation class-recovery equation differs from the given
universal bundle only by its actual base line bundle. The existing proper,
flat, geometrically integral relative Picard comparison removes that base
class. The same supplied representing equivalence therefore classifies
the positive evaluation divisor by the ORIGINAL degree-g translated
identity-component inclusion, on the entire retained parameter scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Modules.Invertible Scheme.Cohomology Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual positive evaluation bundle has the same whole relative
Picard class as the original restricted universal pair. -/
theorem thetaEvaluation_relativeClass :
    (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app
      (op (thetaParameterOver hX o ho P R))
      (classOf _ (thetaEvaluationPositiveLineBundle hX o ho P R)) =
    (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app
      (op (thetaParameterOver hX o ho P R))
      (classOf _ (thetaUniversalPair hX o ho P R).bundle) := by
  let := hX.proper
  let := hX.flat
  let := hX.isGeometricallyIntegral
  have := thetaParameter_isLocallyNoetherian hX o ho P R
  let p := pullback.snd X.hom (thetaParameterOver hX o ho P R).hom
  have : IsProper p := thetaFamily_isProper hX o ho P R
  have : SmoothOfRelativeDimension 1 p := thetaFamily_smoothOfRelativeDimension hX o ho P R
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  let L := (thetaUniversalPair hX o ho P R).bundle
  let B := thetaEvaluationPositiveLineBundle hX o ho P R
  let Q := directImageLineBundle p L (thetaUniversalPair_concentrated hX o ho P R)
  have hrec : classOf _ L = classOf _ B + pullbackClass p (classOf _ Q) :=
    thetaEvaluation_class_recovery hX o ho P R
  apply (quotientProjection_comp_toFppfPicardSheaf_app_eq_iff X.hom
    (T := thetaParameterOver hX o ho P R) _ _).mpr
  refine ⟨-classOf _ Q, ?_⟩
  change classOf _ B = classOf _ L + pullbackClass p (-classOf _ Q)
  rw [PullbackTensor.Local.pullbackClass_neg]
  exact (eq_sub_iff_add_eq.mpr hrec.symm).trans (sub_eq_add_neg _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The entire actual evaluation divisor has the original degree-g
classifying map into the same P/R, before evaluation at any field point. -/
theorem thetaEvaluation_fppfClass :
    letI := picardCommGrpObj X.hom P R
    let T : LocallyNoetherianOver (Spec (.of k)) :=
      ⟨thetaParameterOver hX o ho P R, thetaParameter_isLocallyNoetherian hX o ho P R⟩
    (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op T.obj)
      (classOf _ (thetaEvaluationPositiveLineBundle hX o ho P R)) =
      R.homEquiv (ObjectProperty.homMk (thetaParameterι hX o ho P R ≫
        identityComponentι P.obj ≫ (GrpObj.mulRight (picardPoint P R
          (coherentGenus k X • classOf X.left
            (PointDivisor.positiveLineBundle X hX o ho)))).hom) : T ⟶ P) := by
  let := picardCommGrpObj X.hom P R
  let T : LocallyNoetherianOver (Spec (.of k)) :=
    ⟨thetaParameterOver hX o ho P R, thetaParameter_isLocallyNoetherian hX o ho P R⟩
  exact (thetaEvaluation_relativeClass hX o ho P R).trans
    (degreeUniversalPair_classifies hX o ho P R (coherentGenus k X) (T := T)
      (thetaParameterι hX o ho P R))

end AlgebraicGeometry.Scheme.OverField.Curve
