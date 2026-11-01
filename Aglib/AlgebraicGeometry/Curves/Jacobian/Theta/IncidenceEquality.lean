/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.IncidenceSupport
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.EvaluationTotal
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.ReducedComparison
public import Aglib.AlgebraicGeometry.IdealSheaf.Cartier.Avoidance

/-!
# Equality of the original evaluation divisor and theta incidence

The original rational support calculation identifies the closed points of
the two closed subschemes of the canonical X times V. This ambient scheme
is Jacobson. Both original total schemes are reduced, so the native reduced
closed-subscheme comparison identifies their actual immersions and ideals.
The resulting cartesian square retains the original difference map and
theta inclusion. Smoothness of that difference map then gives the actual
ideal-line-bundle comparison and its positive Picard class.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Opposite AlgebraicGeometry Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open Scheme.Modules.Hom
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original evaluation and incidence immersions have the same range
on the same Jacobson ambient scheme, including nonclosed points. -/
theorem thetaEvaluation_range_eq_thetaIncidence (hg : 0 < coherentGenus k X) :
    Set.range (zeroInclusion (thetaEvaluationContraction hX o ho P R)) =
      Set.range (thetaIncidenceInclusion hX o ho P R) := by
  let := picardCommGrpObj X.hom P R
  have := hX.proper
  let V := thetaParameterOver hX o ho P R
  let Y : FScheme k := X ⊗ V
  have : LocallyOfFiniteType V.hom := by
    change LocallyOfFiniteType
      ((rankOneNonRepeatedOpen hX o ho P R).ι ≫ (identityComponentOver P.obj).hom)
    infer_instance
  have : LocallyOfFiniteType Y.hom := by
    change LocallyOfFiniteType (pullback.fst X.hom V.hom ≫ X.hom)
    infer_instance
  have : JacobsonSpace ↥(pullback (C := Scheme.{u}) X.hom
      (thetaParameterOver hX o ho P R).hom) :=
    LocallyOfFiniteType.jacobsonSpace Y.hom
  let i := zeroInclusion (thetaEvaluationContraction hX o ho P R)
  let j := thetaIncidenceInclusion hX o ho P R
  have : IsClosedImmersion i := zeroInclusion_isClosedImmersion _
  have : IsClosedImmersion j := isClosedImmersion_thetaIncidenceInclusion hX o ho P R
  have hc : Set.range i ∩ closedPoints Y.left = Set.range j ∩ closedPoints Y.left := by
    ext y
    by_cases hy : y ∈ closedPoints Y.left
    · simp only [Set.mem_inter_iff, and_iff_left hy]
      let t : 𝟙_ (Over (Spec (.of k))) ⟶ Y :=
        Over.homMk (pointOfClosedPoint Y.hom y hy) (pointOfClosedPoint_comp Y.hom y hy)
      let q : 𝟙_ (Over (Spec (.of k))) ⟶ X := t ≫ fst X V
      let c : 𝟙_ (Over (Spec (.of k))) ⟶ V := t ≫ snd X V
      have ht : q.left ≫ thetaRationalFamilyMap hX o ho P R c = t.left := by
        rw [thetaRationalFamilyMap_comp_point hX o ho P R c q.left (Over.w q)]
        exact congrArg Over.Hom.left (lift_comp_fst_snd t)
      have hp : t.left (IsLocalRing.closedPoint k) = y :=
        pointOfClosedPoint_apply Y.hom y hy _
      have hp' : (q.left ≫ thetaRationalFamilyMap hX o ho P R c)
          (IsLocalRing.closedPoint k) = y :=
        (congrArg (fun v => v (IsLocalRing.closedPoint k)) ht).trans hp
      have hr : (q.left ≫ thetaRationalFamilyMap hX o ho P R c)
            (IsLocalRing.closedPoint k) ∈ Set.range i ↔
          (q.left ≫ thetaRationalFamilyMap hX o ho P R c)
            (IsLocalRing.closedPoint k) ∈ Set.range j :=
        thetaEvaluation_mem_iff_thetaIncidence_mem hX o ho P R hg c q.left (Over.w q)
      rw [hp'] at hr
      exact hr
    · simp only [Set.mem_inter_iff, hy, and_false]
  calc
    Set.range i = closure (Set.range i ∩ closedPoints Y.left) :=
      (closure_inter_closedPoints i.isClosedEmbedding.isClosed_range).symm
    _ = closure (Set.range j ∩ closedPoints Y.left) := congrArg closure hc
    _ = Set.range j := closure_inter_closedPoints j.isClosedEmbedding.isClosed_range

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical comparison of the two original reduced closed
subschemes, over the unchanged canonical family. -/
def thetaEvaluationIsoIncidence (hg : 0 < coherentGenus k X) :
    zeroScheme (thetaEvaluationContraction hX o ho P R) ≅
      pullback (thetaIncidenceMorphism hX o ho P R).left
        (thetaIncidenceRestrictionMap hX o ho P R).left := by
  have := isReduced_thetaEvaluation hX o ho P R hg
  have := isReduced_thetaIncidence hX o ho P R
  have := isClosedImmersion_thetaIncidenceInclusion hX o ho P R
  exact ReducedClosedSubscheme.ofRangeEq
    (zeroInclusion (thetaEvaluationContraction hX o ho P R))
    (thetaIncidenceInclusion hX o ho P R)
    (thetaEvaluation_range_eq_thetaIncidence hX o ho P R hg)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
theorem thetaEvaluationIsoIncidence_hom_inclusion (hg : 0 < coherentGenus k X) :
    (thetaEvaluationIsoIncidence hX o ho P R hg).hom ≫ thetaIncidenceInclusion hX o ho P R =
      zeroInclusion (thetaEvaluationContraction hX o ho P R) := by
  have := isReduced_thetaEvaluation hX o ho P R hg
  have := isReduced_thetaIncidence hX o ho P R
  have := isClosedImmersion_thetaIncidenceInclusion hX o ho P R
  have : IsClosedImmersion (zeroInclusion (thetaEvaluationContraction hX o ho P R)) :=
    zeroInclusion_isClosedImmersion _
  exact ReducedClosedSubscheme.of_range_eq_hom_fac
    (zeroInclusion (thetaEvaluationContraction hX o ho P R))
    (thetaIncidenceInclusion hX o ho P R)
    (thetaEvaluation_range_eq_thetaIncidence hX o ho P R hg)

/-- Equality of the original kernel ideal sheaves, not merely their supports. -/
theorem thetaEvaluation_ker_eq_thetaIncidence (hg : 0 < coherentGenus k X) :
    (zeroInclusion (thetaEvaluationContraction hX o ho P R)).ker =
      (thetaIncidenceInclusion hX o ho P R).ker := by
  rw [← thetaEvaluationIsoIncidence_hom_inclusion hX o ho P R hg, Hom.ker_comp_of_isIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original evaluation divisor itself is the pullback of the
original theta immersion by the original difference map on X times V. -/
theorem isPullback_thetaEvaluation (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    IsPullback
      ((thetaEvaluationIsoIncidence hX o ho P R hg).hom ≫
        pullback.fst (thetaIncidenceMorphism hX o ho P R).left
          (thetaIncidenceRestrictionMap hX o ho P R).left ≫
            (fst (thetaImageOver hX o ho P R) X).left)
      (zeroInclusion (thetaEvaluationContraction hX o ho P R))
      (thetaImageInclusion hX o ho P R).left (thetaIncidenceDifference hX o ho P R).left := by
  let := picardCommGrpObj X.hom P R
  have H : IsPullback (thetaEvaluationIsoIncidence hX o ho P R hg).hom
      (zeroInclusion (thetaEvaluationContraction hX o ho P R))
      (thetaIncidenceInclusion hX o ho P R) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp only [Category.comp_id,
      thetaEvaluationIsoIncidence_hom_inclusion]⟩
  simpa only [Category.id_comp] using H.paste_horiz (isPullback_thetaIncidence hX o ho P R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Literal equality with the inverse-image theta ideal on the original ambient scheme. -/
theorem thetaEvaluation_ker_eq_comap_theta (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    (zeroInclusion (thetaEvaluationContraction hX o ho P R)).ker =
      (thetaImageInclusion hX o ho P R).left.ker.comap
        (thetaIncidenceDifference hX o ho P R).left := by
  let := picardCommGrpObj X.hom P R
  have : IsClosedImmersion (thetaImageInclusion hX o ho P R).left :=
    (isEffectiveCartier_basedAbelImage_pred hX o ho P R hg).isClosedImmersion
  exact Hom.ker_eq_comap_of_isPullback_of_isClosedImmersion _ _ _ _
    (isPullback_thetaEvaluation hX o ho P R hg)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original positive theta line bundle pulls back to the original
positive evaluation-divisor class. No Cartier pullback along the Abel curve
morphism alone is used. -/
theorem thetaEvaluation_positiveClass_eq (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    pullbackClass (thetaIncidenceDifference hX o ho P R).left
      (classOf _ (thetaLineBundle hX o ho P R hg)) =
        classOf _ (thetaEvaluationPositiveLineBundle hX o ho P R) := by
  let := picardCommGrpObj X.hom P R
  let H := isPullback_thetaEvaluation hX o ho P R hg
  let hTheta := isEffectiveCartier_basedAbelImage_pred hX o ho P R hg
  let hD := thetaEvaluation_isRelativeEffectiveCartier hX o ho P R
  have : IsClosedImmersion (thetaImageInclusion hX o ho P R).left := hTheta.isClosedImmersion
  have := smooth_thetaIncidenceDifference hX o ho P R
  let m := Hom.idealPullbackMap (thetaImageInclusion hX o ho P R).left
    (zeroInclusion (thetaEvaluationContraction hX o ho P R))
    (thetaIncidenceDifference hX o ho P R).left _ H.w
  have hm : IsIso m := Hom.idealPullbackMap_isIso_of_flat (thetaImageInclusion hX o ho P R).left
    (thetaIncidenceDifference hX o ho P R).left
    (zeroInclusion (thetaEvaluationContraction hX o ho P R)) _ H.w H
  have hc : pullbackClass (thetaIncidenceDifference hX o ho P R).left
      (classOf _ hTheta.idealLineBundle) = classOf _ hD.idealLineBundle :=
    Quotient.sound ⟨@asIso _ _ _ _ m hm⟩
  rw [classOf_thetaLineBundle, PullbackTensor.Local.pullbackClass_neg, hc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The class comparison supplies an actual isomorphism of the original
positive line bundles on the entire retained parameter open. -/
theorem thetaEvaluation_positiveLineBundle_iso (hg : 0 < coherentGenus k X) :
    letI := picardCommGrpObj X.hom P R
    Nonempty ((pullbackLineBundle (thetaIncidenceDifference hX o ho P R).left
      (thetaLineBundle hX o ho P R hg)).val ≅
        (thetaEvaluationPositiveLineBundle hX o ho P R).val) := by
  let := picardCommGrpObj X.hom P R
  exact (class_eq_iff _ _ _).mp (thetaEvaluation_positiveClass_eq hX o ho P R hg)

end AlgebraicGeometry.Scheme.OverField.Curve
