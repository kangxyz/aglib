/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.RationalEvaluation
public import Aglib.AlgebraicGeometry.Curves.Abel.RankOneSupport
public import Aglib.AlgebraicGeometry.Curves.Picard.PointDegree

/-!
# Rational support and degree of the original evaluation divisor

Specialize the original evaluation immersion through its actual cartesian
square on X. Its positive coefficient has h0=1 and H1=0. The generic
rank-one Cartier support theorem therefore identifies membership with a
nonzero section after twisting by the ORIGINAL point ideal. Riemann--Roch
computes degree g, so that this point twist has degree g-1.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Modules Scheme.Modules.Hom Scheme.Modules.Invertible
open Scheme.Cohomology Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

open Picard Picard.DivisorClass Picard.Degree

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]
  (c : 𝟙_ (Over (Spec (.of k))) ⟶ thetaParameterOver hX o ho P R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual rational coefficient has h0 equal to one. -/
theorem thetaRationalEvaluation_h0 :
    Module.finrank k (moduleCohomology k X
      (thetaRationalEvaluationLineBundle hX o ho P R c).val 0) = 1 :=
  (thetaRationalEvaluation_dimension hX o ho P R c 0).trans
    (thetaUniversalPair_concentrated hX o ho P R k c.left).1

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual rational coefficient has zero H1 dimension. -/
theorem thetaRationalEvaluation_h1 :
    Module.finrank k (moduleCohomology k X
      (thetaRationalEvaluationLineBundle hX o ho P R c).val 1) = 0 := by
  have := (thetaUniversalPair_concentrated hX o ho P R k c.left).2 1 (by omega)
  exact (thetaRationalEvaluation_dimension hX o ho P R c 1).trans
    Module.finrank_zero_of_subsingleton

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original evaluation support at the rational pair is exactly a
nonzero section of the original coefficient twisted by the point ideal. -/
theorem thetaEvaluation_mem_range_iff_nonzero_point_twist
    (q : Spec (.of k) ⟶ X.left) (hq : q ≫ X.hom = 𝟙 _) :
    (q ≫ thetaRationalFamilyMap hX o ho P R c) (IsLocalRing.closedPoint k) ∈
      Set.range (zeroInclusion (thetaEvaluationContraction hX o ho P R)) ↔
    ∃ s : (tensorLineBundle X.left (thetaRationalEvaluationLineBundle hX o ho P R c)
      (PointDivisor.idealLineBundle X hX q hq)).val.val.obj (op ⊤), s ≠ 0 := by
  let i := thetaRationalEvaluationInclusion hX o ho P R c
  let hD := thetaRationalEvaluation_isRelativeEffectiveCartier hX o ho P R c
  have : IsClosedImmersion i := hD.isClosedImmersion
  have : IsFinite (i ≫ X.hom) := thetaRationalEvaluation_finite hX o ho P R c
  let B := dualLineBundle X.left hD.idealLineBundle
  let L := thetaRationalEvaluationLineBundle hX o ho P R c
  have hc : classOf X.left B = classOf X.left L := thetaRationalEvaluation_idealClass hX o ho P R c
  obtain ⟨E⟩ := (class_eq_iff X.left B L).mp hc
  have hB0 : Module.finrank k (moduleCohomology k X B.val 0) = 1 :=
    (moduleCohomologyIso X E 0).finrank_eq.trans (thetaRationalEvaluation_h0 hX o ho P R c)
  have hsupport := Abel.finiteCartier_mem_range_iff_nonzero_point_twist
    hX i hD.isLocallyRankOne hB0 q hq
  have hrange : Set.range i = (thetaRationalFamilyMap hX o ho P R c) ⁻¹'
      Set.range (zeroInclusion (thetaEvaluationContraction hX o ho P R)) :=
    Scheme.Pullback.range_snd _ _
  rw [hrange] at hsupport
  refine hsupport.trans ?_
  let := PointDivisor.isIntegral_of_properties X hX
  let := curveProperties_isNoetherian hX
  let (x : ClosedPoint X.left) := PointDivisor.isDiscreteValuationRing_stalk X hX x
  let hd := (curveProperties_dimension smoothFieldDimension hX).le
  change (∃ s : (tensorLineBundle X.left B
    (PointDivisor.idealLineBundle X hX q hq)).val.val.obj (op ⊤), s ≠ 0) ↔
    ∃ s : (tensorLineBundle X.left L
      (PointDivisor.idealLineBundle X hX q hq)).val.val.obj (op ⊤), s ≠ 0
  rw [exists_nonzero_section_iff_effective_class X.left hd,
    exists_nonzero_section_iff_effective_class X.left hd]
  simp only [classOf_tensor, hc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual rational coefficient has degree the original genus. -/
theorem thetaRationalEvaluation_degree :
    curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension properCurveProductFormula
      X hX (classOf X.left (thetaRationalEvaluationLineBundle hX o ho P R c)) =
        (coherentGenus k X : ℤ) := by
  let := hX.proper
  let := PointDivisor.isIntegral_of_properties X hX
  let := curveProperties_isNoetherian hX
  let (x : ClosedPoint X.left) := PointDivisor.isDiscreteValuationRing_stalk X hX x
  let hd := (curveProperties_dimension smoothFieldDimension hX)
  let L := thetaRationalEvaluationLineBundle hX o ho P R c
  have hrr := lineBundleRiemannRoch k X hd.le
    (properCurveProductFormula k X.left X.hom hd) L inferInstance
    (constants_bijective_of_proper_of_isAlgClosed X)
  have h0 := thetaRationalEvaluation_h0 hX o ho P R c
  have h1 := thetaRationalEvaluation_h1 hX o ho P R c
  change lineBundleDegree X.left X.hom hd.le
    (properCurveProductFormula k X.left X.hom hd) L = (coherentGenus k X : ℤ)
  rw [h0, h1] at hrr
  omega

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Twisting by the ORIGINAL point ideal has degree g-1, with the
natural/integer predecessor conversion retained explicitly. -/
theorem thetaRationalEvaluation_pointTwist_degree (hg : 0 < coherentGenus k X)
    (q : Spec (.of k) ⟶ X.left) (hq : q ≫ X.hom = 𝟙 _) :
    curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension properCurveProductFormula X hX
      (classOf X.left (tensorLineBundle X.left (thetaRationalEvaluationLineBundle hX o ho P R c)
        (PointDivisor.idealLineBundle X hX q hq))) = ((coherentGenus k X - 1 : ℕ) : ℤ) := by
  let deg := curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
    smoothClosedPointDimension smoothFieldDimension properCurveProductFormula X hX
  have hpoint := curveDegree_positiveLineBundle hX q hq
  change deg (-classOf X.left (PointDivisor.idealLineBundle X hX q hq)) = 1 at hpoint
  rw [map_neg] at hpoint
  rw [classOf_tensor, map_add, thetaRationalEvaluation_degree]
  change (coherentGenus k X : ℤ) + deg (classOf X.left
    (PointDivisor.idealLineBundle X hX q hq)) = ((coherentGenus k X - 1 : ℕ) : ℤ)
  omega

end AlgebraicGeometry.Scheme.OverField.Curve
