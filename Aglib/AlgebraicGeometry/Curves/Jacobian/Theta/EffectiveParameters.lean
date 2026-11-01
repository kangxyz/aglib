/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.RationalPoints
public import Aglib.AlgebraicGeometry.Curves.Jacobian.PicardScheme
public import Aglib.AlgebraicGeometry.Curves.Picard.EffectiveClass

/-!
# Nonzero sections produce actual Abel parameters in their own degree

On an algebraically closed field, a nonzero section of a degree-n line
bundle gives an effective divisor of degree n. Decomposing that actual
divisor into rational points produces an actual point of the existing
ordered graph family. Its Abel image in the same supplied Picard scheme is
the original class minus n times the fixed positive point class.

There is no genus inequality in this statement. In particular it applies
to degree g-1 in the theta effective-locus argument. The construction reuses
the existing divisor, point-ideal, family and Picard classifying maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Modules.Invertible Scheme.RelativePicard
open Scheme.OverField.Curve.Divisors

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

open Picard Picard.DivisorClass Picard.Degree

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

-- Match the existing divisor/Picard and identity-fibre presentations throughout.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Any nonzero section in nonnegative degree produces an actual rational
parameter of the same degree for the original based Abel morphism. -/
theorem exists_comp_abelMorphism_of_nonzero_section (n : ℕ) (L : LineBundle X.left)
    (hdegree : curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension properCurveProductFormula
      X hX (classOf X.left L) = (n : ℤ))
    (s : L.val.val.obj (op ⊤)) (hs : s ≠ 0) :
    letI := hX.smooth
    letI := hX.proper
    ∃ a : 𝟙_ (Over (Spec (.of k))) ⟶ parameter X.hom n,
      a ≫ (abelMorphism o ho P R n).hom =
        picardPoint P R (classOf X.left L -
          n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)) := by
  let := hX.smooth
  let := hX.proper
  let := PointDivisor.isIntegral_of_properties X hX
  let := curveProperties_isNoetherian hX
  let (x : ClosedPoint X.left) : IsDiscreteValuationRing (X.left.presheaf.stalk x.val) :=
    PointDivisor.isDiscreteValuationRing_stalk X hX x
  let hd := hX.topologicalKrullDim_eq_one
  obtain ⟨D, hD, hclass⟩ :=
    exists_effective_divisor_class_of_nonzero_section X.left hd.le L s hs
  have hdegree' : picardDegree X.left X.hom hd.le
      (properCurveProductFormula k X.left X.hom hd) (classOf X.left L) = (n : ℤ) := hdegree
  have hdeg : degDiv X.left X.hom D = (n : ℤ) := by
    rw [← picardDegree_divisor X.left X.hom hd.le
      (properCurveProductFormula k X.left X.hom hd)]
    exact (congrArg (picardDegree X.left X.hom hd.le
      (properCurveProductFormula k X.left X.hom hd)) hclass).trans hdegree'
  obtain ⟨t, ht⟩ := effective_divisor_eq_sum_points X.left X.hom n D hD hdeg
  let q : Fin n → {q : Spec (.of k) ⟶ X.left // q ≫ X.hom = 𝟙 _} := fun i =>
    ⟨pointOfClosedPoint X.hom (t i).val (t i).property,
      pointOfClosedPoint_comp X.hom (t i).val (t i).property⟩
  have hq (i : Fin n) : PointDivisor.closedPoint X (q i).val (q i).property = t i := by
    apply Subtype.ext
    exact pointOfClosedPoint_apply X.hom (t i).val (t i).property _
  have hsum : classOf X.left L = ∑ i : Fin n,
      classOf X.left (PointDivisor.positiveLineBundle X hX (q i).val (q i).property) := by
    rw [← hclass, ht, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [PointDivisor.positiveLineBundle_class_eq_pointDivisor X hX
      (q i).val (q i).property hd.le]
    simp only [PointDivisor.pointDivisor, hq]
  have hnormalized : classOf X.left L -
      n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho) =
      ∑ i : Fin n,
        (classOf X.left (PointDivisor.positiveLineBundle X hX (q i).val (q i).property) -
          classOf X.left (PointDivisor.positiveLineBundle X hX o ho)) := by
    rw [hsum, Finset.sum_sub_distrib]
    simp
  let a := parameterPoint X.hom (𝟙 _) (fun i => (q i).val) (fun i => (q i).property)
  have ha : a ≫ (parameter X.hom n).hom = 𝟙 _ :=
    parameterPoint_over X.hom (𝟙 _) _ _
  refine ⟨Over.homMk a ha, parameterPoint_comp_abelMorphism_eq_picardPoint o ho P R a ha _ ?_⟩
  rw [lineBundle_class_at_tuple, hnormalized]
  change (PullbackTensor.Local.pullbackHom _) (∑ i : Fin n, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact pointDifference_class_pullback_identity X hX o ho (q i).val (q i).property

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
