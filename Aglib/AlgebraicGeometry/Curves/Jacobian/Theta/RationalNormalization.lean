/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.RationalSupport
public import Aglib.AlgebraicGeometry.Curves.Jacobian.AbelCurve

/-!
# The original normalized point-twist class

The actual degree-g evaluation coefficient has class a+g[o]. Twisting by
the original ideal of q and normalizing degree g-1 therefore gives the
original difference a-f_o(q). All equations here are between the original
scheme morphisms into the same P and its same identity component.
The Abel convention remains f_o(q)=[q-o].
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open Opposite AlgebraicGeometry Scheme Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Abel.BoundedFamily

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

include hX o ho in
omit [IsSeparated P.obj.hom] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem picardPoint_sub_class (A B : PicardGroup X.left) :
    letI := picardCommGrpObj X.hom P R
    picardPoint P R (A - B) = picardPoint P R A / picardPoint P R B := by
  let := picardCommGrpObj X.hom P R
  have := hX.proper
  have := hX.flat
  have := hX.isGeometricallyIntegral
  have : IsSplitEpi X.hom := IsSplitEpi.mk' ⟨o, ho⟩
  let e := picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral P R
  have h := congrArg Additive.toMul (e.map_sub A B)
  change Additive.toMul (e (A - B)) = Additive.toMul (e A) / Additive.toMul (e B) at h
  simpa only [e,
    picardPointAddEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_apply] using h

omit [IsSeparated P.obj.hom] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original based Abel curve morphism has its original rational
class [q-o], without changing the selected curve or Picard representative. -/
theorem jacobianCurveMorphism_rational_class
    (q : Spec (.of k) ⟶ X.left) (hq : q ≫ X.hom = 𝟙 _) :
    letI := picardCommGrpObj X.hom P R
    (Over.homMk q hq : 𝟙_ (Over (Spec (.of k))) ⟶ X) ≫
      jacobianCurveMorphism hX o ho P R ≫ identityComponentι P.obj =
        picardPoint P R (classOf X.left (PointDivisor.positiveLineBundle X hX q hq) -
          classOf X.left (PointDivisor.positiveLineBundle X hX o ho)) := by
  let := picardCommGrpObj X.hom P R
  have := hX.smooth
  have := hX.proper
  rw [jacobianCurveMorphism_comp_inclusion, ← Category.assoc, comp_singleParameterMorphism]
  apply parameterPoint_comp_abelMorphism_eq_picardPoint o ho P R
  change pullbackClass (pullback.fst X.hom (𝟙 (Spec (.of k))))
      (classOf X.left (PointDivisor.positiveLineBundle X hX q hq) -
        classOf X.left (PointDivisor.positiveLineBundle X hX o ho)) =
    pullbackClass (Hom.familyMap X.hom (parameter X.hom 1).hom (𝟙 (Spec (.of k)))
      (parameterPoint X.hom (𝟙 (Spec (.of k))) (fun _ : Fin 1 => q) (fun _ => hq))
      (parameterPoint_over X.hom (𝟙 (Spec (.of k))) _ _))
      (classOf _ (lineBundle X.hom o ho 1))
  rw [lineBundle_class_at_tuple]
  simpa only [Fin.sum_univ_one] using pointDifference_class_pullback_identity X hX o ho q hq

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degree-(g-1) normalized class of the actual point-twisted
rational evaluation coefficient is the original a-f_o(q). -/
theorem thetaRationalEvaluation_pointTwist_normalized_class (hg : 0 < coherentGenus k X)
    (c : 𝟙_ (Over (Spec (.of k))) ⟶ thetaParameterOver hX o ho P R)
    (q : Spec (.of k) ⟶ X.left) (hq : q ≫ X.hom = 𝟙 _) :
    letI := picardCommGrpObj X.hom P R
    ((c ≫ thetaParameterι hX o ho P R) /
      ((Over.homMk q hq : 𝟙_ (Over (Spec (.of k))) ⟶ X) ≫
        jacobianCurveMorphism hX o ho P R)) ≫ identityComponentι P.obj =
      picardPoint P R (classOf X.left
        (tensorLineBundle X.left (thetaRationalEvaluationLineBundle hX o ho P R c)
          (PointDivisor.idealLineBundle X hX q hq)) -
        (coherentGenus k X - 1) • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)) := by
  let := picardCommGrpObj X.hom P R
  let A := classOf X.left (thetaRationalEvaluationLineBundle hX o ho P R c)
  let O := classOf X.left (PointDivisor.positiveLineBundle X hX o ho)
  let Q := classOf X.left (PointDivisor.positiveLineBundle X hX q hq)
  have hIq : classOf X.left (PointDivisor.idealLineBundle X hX q hq) = -Q := by
    change _ = -(-classOf X.left (PointDivisor.idealLineBundle X hX q hq))
    exact (neg_neg _).symm
  have hnorm : classOf X.left
      (tensorLineBundle X.left (thetaRationalEvaluationLineBundle hX o ho P R c)
        (PointDivisor.idealLineBundle X hX q hq)) - (coherentGenus k X - 1) • O =
        (A - coherentGenus k X • O) - (Q - O) := by
    rw [classOf_tensor, hIq]
    have hg' : coherentGenus k X = (coherentGenus k X - 1) + 1 :=
      (Nat.sub_add_cancel hg).symm
    nth_rw 2 [hg']
    rw [add_nsmul, one_nsmul]
    abel
  have hL : picardPoint P R A =
      (c ≫ thetaParameterι hX o ho P R ≫ identityComponentι P.obj) *
        picardPoint P R (coherentGenus k X • O) := by
    have h := thetaRationalEvaluation_picardPoint hX o ho P R c
    simpa only [GrpObj.mulRight, CategoryTheory.Hom.mul_def, comp_lift_assoc,
      Category.comp_id, comp_toUnit_assoc, toUnit_unit, Category.id_comp] using h
  rw [GrpObj.div_comp, hnorm, picardPoint_sub_class hX o ho P R,
    picardPoint_sub_class hX o ho P R, hL, mul_div_cancel_right,
    ← jacobianCurveMorphism_rational_class hX o ho P R q hq]
  rfl

end AlgebraicGeometry.Scheme.OverField.Curve
