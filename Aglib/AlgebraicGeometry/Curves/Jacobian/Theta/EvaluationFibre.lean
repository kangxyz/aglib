/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.EvaluationFamily
public import Aglib.AlgebraicGeometry.Picard.Abel.Basic

/-!
# Actual field fibres of theta evaluation

The original family square identifies the canonical curve over the field
with the original evaluation family fibre. The divisor is the literal
pullback of the existing evaluation immersion. Its ideal comparison is
invertible because that original divisor is flat over the parameter base;
the field-valued parameter itself need not be flat.

The positive ideal class is the actual pulled universal class. The
canonical fibre isomorphism and its second projection preserve the field
action before cohomology dimensions are compared.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Modules Scheme.Modules.Hom Scheme.Modules.Invertible
open Scheme.Cohomology Scheme.RelativePicard Scheme.Group
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
  {K : Type u} [Field K] (b : Spec (.of K) ⟶ Spec (.of k))
  (a : Over.mk b ⟶ thetaParameterOver hX o ho P R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original evaluation immersion pulled back to the canonical field
curve is an actual relative effective Cartier divisor. -/
theorem thetaEvaluationFibre_isRelativeEffectiveCartier :
    Hom.IsRelativeEffectiveCartier
      (pullback.snd (zeroInclusion (thetaEvaluationContraction hX o ho P R))
        ((familyScheme X.hom).map a)) (pullback.snd X.hom b) :=
  (thetaEvaluation_isRelativeEffectiveCartier hX o ho P R).of_isPullback
    (isPullback_familyScheme_map X.hom a) (IsPullback.of_hasPullback _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- This literal pulled divisor is finite over the original field. -/
theorem thetaEvaluationFibre_finite :
    IsFinite (pullback.snd (zeroInclusion (thetaEvaluationContraction hX o ho P R))
      ((familyScheme X.hom).map a) ≫ pullback.snd X.hom b) :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback _ _).paste_vert (isPullback_familyScheme_map X.hom a))
    (thetaEvaluation_finite_flat hX o ho P R).1

/-- The positive bundle of that same literal field divisor. -/
def thetaEvaluationFibrePositiveLineBundle : LineBundle (pullback X.hom b) :=
  dualLineBundle _ (thetaEvaluationFibre_isRelativeEffectiveCartier hX o ho P R b a).idealLineBundle

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Its actual positive ideal class is the original universal fibre class;
the base correction vanishes only after pullback to the field. -/
theorem thetaEvaluationFibre_class :
    classOf _ (thetaEvaluationFibrePositiveLineBundle hX o ho P R b a) =
      classOf _ (RigidifiedPair.map a (thetaUniversalPair hX o ho P R)).bundle := by
  let p := pullback.snd X.hom (thetaParameterOver hX o ho P R).hom
  let L := (thetaUniversalPair hX o ho P R).bundle
  let m : pullback X.hom b ⟶ pullback X.hom (thetaParameterOver hX o ho P R).hom :=
    (familyScheme X.hom).map a
  let H := isPullback_familyScheme_map X.hom a
  let hD := thetaEvaluation_isRelativeEffectiveCartier hX o ho P R
  have hid := hD.pullbackClass_classOf_idealLineBundle H (IsPullback.of_hasPullback _ _)
  have hpos : classOf _ (thetaEvaluationFibrePositiveLineBundle hX o ho P R b a) =
      pullbackClass m (classOf _ (thetaEvaluationPositiveLineBundle hX o ho P R)) := by
    change -classOf _
      (thetaEvaluationFibre_isRelativeEffectiveCartier hX o ho P R b a).idealLineBundle =
        pullbackClass m (-classOf _ hD.idealLineBundle)
    rw [PullbackTensor.Local.pullbackClass_neg]
    exact congrArg Neg.neg hid.symm
  have := thetaParameter_isLocallyNoetherian hX o ho P R
  have : IsProper p := thetaFamily_isProper hX o ho P R
  have : SmoothOfRelativeDimension 1 p := thetaFamily_smoothOfRelativeDimension hX o ho P R
  have : Smooth p := SmoothOfRelativeDimension.smooth 1 p
  let Q := directImageLineBundle p L (thetaUniversalPair_concentrated hX o ho P R)
  have hbase : pullbackClass m (pullbackClass p (classOf _ Q)) = 0 := by
    rw [← pullbackClass_comp, H.w, pullbackClass_comp,
      Hom.fieldPicard_eq_zero K (pullbackClass a.left (classOf _ Q)), pullbackClass_zero]
  have hrec := congrArg (pullbackClass m) (thetaEvaluation_class_recovery hX o ho P R)
  rw [PullbackTensor.Local.pullbackClass_add, hbase, add_zero] at hrec
  exact hpos.trans (hrec.symm.trans (pullbackClass_classOf m L))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual composition comparison returns the same original degree-g
universal pair on the same Jacobian. -/
theorem thetaEvaluationFibre_degreeUniversalClass :
    letI := picardCommGrpObj X.hom P R
    classOf _ (thetaEvaluationFibrePositiveLineBundle hX o ho P R b a) =
      classOf _ (RigidifiedPair.map (a ≫ thetaParameterι hX o ho P R)
        (degreeUniversalPair hX o ho P R (coherentGenus k X))).bundle := by
  let := picardCommGrpObj X.hom P R
  exact (thetaEvaluationFibre_class hX o ho P R b a).trans
    (Quotient.sound ⟨(RigidifiedPair.mapCompIso a (thetaParameterι hX o ho P R)
      (degreeUniversalPair hX o ho P R (coherentGenus k X))).iso.symm⟩)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual marked fibre isomorphism compares cohomology with the
original concentrated family, preserving the structural K-action. -/
theorem thetaEvaluationFibre_dimension (n : ℕ) :
    let Y : FScheme K := Over.mk (pullback.snd X.hom b)
    let B : LineBundle Y.left := thetaEvaluationFibrePositiveLineBundle hX o ho P R b a
    Module.finrank K (moduleCohomology K Y B.val n) =
      Module.finrank K (fibreCohomology
        (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom)
        (thetaUniversalPair hX o ho P R).bundle.val K a.left n) := by
  let Y : FScheme K := Over.mk (pullback.snd X.hom b)
  let B : LineBundle Y.left := thetaEvaluationFibrePositiveLineBundle hX o ho P R b a
  change Module.finrank K (moduleCohomology K Y B.val n) = _
  let p := pullback.snd X.hom (thetaParameterOver hX o ho P R).hom
  let L := (thetaUniversalPair hX o ho P R).bundle
  let m : pullback X.hom b ⟶ pullback X.hom (thetaParameterOver hX o ho P R).hom :=
    (familyScheme X.hom).map a
  let H := isPullback_familyScheme_map X.hom a
  let e := H.isoPullback
  have he : e.hom ≫ pullback.fst p a.left = m := H.isoPullback_hom_fst
  have hs : e.hom ≫ pullback.snd p a.left = pullback.snd X.hom b :=
    H.isoPullback_hom_snd
  let C : (Scheme.Modules.pullback e.hom).obj
      ((Scheme.Modules.pullback (pullback.fst p a.left)).obj L.val) ≅
      (RigidifiedPair.map a (thetaUniversalPair hX o ho P R)).bundle.val :=
    (Scheme.Modules.pullbackComp e.hom (pullback.fst p a.left)).app L.val ≪≫
      (Scheme.Modules.pullbackCongr he).app L.val
  obtain ⟨E⟩ := (class_eq_iff Y.left B
    (RigidifiedPair.map a (thetaUniversalPair hX o ho P R)).bundle).mp
      (thetaEvaluationFibre_class hX o ho P R b a)
  calc
    _ = moduleCohomologyDimension (pullback.snd X.hom b) B.val n :=
      (moduleCohomologyDimension_eq_finrank_moduleCohomology Y B.val n).symm
    _ = moduleCohomologyDimension (pullback.snd X.hom b)
        (RigidifiedPair.map a (thetaUniversalPair hX o ho P R)).bundle.val n :=
      moduleCohomologyDimension_congr (pullback.snd X.hom b) E n
    _ = moduleCohomologyDimension (pullback.snd p a.left)
        ((Scheme.Modules.pullback (pullback.fst p a.left)).obj L.val) n :=
      (moduleCohomologyDimension_eq_of_isIso e.hom (pullback.snd p a.left)
        (pullback.snd X.hom b) hs
        ((Scheme.Modules.pullback (pullback.fst p a.left)).obj L.val) C n).symm
    _ = _ := moduleCohomologyDimension_eq_finrank_moduleCohomology
      (Over.mk (pullback.snd p a.left) : FScheme K)
      ((Scheme.Modules.pullback (pullback.fst p a.left)).obj L.val) n

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual geometric evaluation fibres have h0 equal to one. -/
theorem thetaEvaluationFibre_h0 [IsAlgClosed K] :
    let Y : FScheme K := Over.mk (pullback.snd X.hom b)
    let B : LineBundle Y.left := thetaEvaluationFibrePositiveLineBundle hX o ho P R b a
    Module.finrank K (moduleCohomology K Y B.val 0) = 1 :=
  (thetaEvaluationFibre_dimension hX o ho P R b a 0).trans
    (thetaUniversalPair_concentrated hX o ho P R K a.left).1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual geometric evaluation fibres have vanishing H1 dimension. -/
theorem thetaEvaluationFibre_h1 [IsAlgClosed K] :
    let Y : FScheme K := Over.mk (pullback.snd X.hom b)
    let B : LineBundle Y.left := thetaEvaluationFibrePositiveLineBundle hX o ho P R b a
    Module.finrank K (moduleCohomology K Y B.val 1) = 0 := by
  have := (thetaUniversalPair_concentrated hX o ho P R K a.left).2 1 (by omega)
  exact (thetaEvaluationFibre_dimension hX o ho P R b a 1).trans
    Module.finrank_zero_of_subsingleton

end AlgebraicGeometry.Scheme.OverField.Curve
