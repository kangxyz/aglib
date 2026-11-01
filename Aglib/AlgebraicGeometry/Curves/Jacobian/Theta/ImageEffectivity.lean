/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.AbelGeometry
public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.EffectiveParameters
public import Aglib.AlgebraicGeometry.RationalPoint.ProperImage

/-!
# Effective-locus support of the original based Abel image

The original proper image membership criterion lifts the specified field
point through the same ordered Abel parameter. Its original graph-family
class is a sum of actual positive point classes. Conversely, a nonzero
section gives a parameter of the specified degree by the existing native
effective-divisor construction. Both directions retain the same P/R and
the original normalization by n times the chosen point.

This is a support statement after the whole classifying morphisms and
actual schematic image have already been constructed. It does not replace
the image ideal or assert an isomorphism from pointwise information alone.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Cohomology Scheme.Modules.Invertible Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily

open Picard Picard.DivisorClass Picard.Degree Divisors

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
/-- Membership in the original degree-n based schematic Abel image is
exactly effectivity of the original degree-n line bundle. -/
theorem mem_basedAbelImage_iff_nonzero_section (n : ℕ) (L : LineBundle X.left)
    (hdegree : curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
      smoothClosedPointDimension smoothFieldDimension properCurveProductFormula
      X hX (classOf X.left L) = (n : ℤ)) :
    letI := picardCommGrpObj X.hom P R
    ∀ (a : 𝟙_ (Over (Spec (.of k))) ⟶ identityComponentOver P.obj),
      a ≫ identityComponentι P.obj = picardPoint P R (classOf X.left L -
        n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)) →
      (a.left (IsLocalRing.closedPoint k) ∈
        Set.range (jacobianAbelMorphism hX o ho P R n).left.imageι ↔
        ∃ s : L.val.val.obj (op ⊤), s ≠ 0) := by
  classical
  let := picardCommGrpObj X.hom P R
  let := hX.smooth
  let := hX.proper
  let := hX.flat
  let := hX.isGeometricallyIntegral
  let := PointDivisor.isIntegral_of_properties X hX
  let := curveProperties_isNoetherian hX
  let (x : ClosedPoint X.left) := PointDivisor.isDiscreteValuationRing_stalk X hX x
  have : IsSplitEpi X.hom := IsSplitEpi.mk' ⟨o, ho⟩
  let hd := hX.topologicalKrullDim_eq_one.le
  let F := jacobianAbelMorphism hX o ho P R n
  have : IsProper F.left := isProper_jacobianAbelMorphism hX o ho P R n
  intro a haclass
  constructor
  · intro ha
    obtain ⟨u, hu⟩ := (F.left.mem_image_iff_exists_lift_spec k a.left).mp ha
    have huover : u ≫ (parameter X.hom n).hom = 𝟙 _ := by
      rw [← Over.w F, ← Category.assoc, hu]
      exact a.w
    let s : 𝟙_ (Over (Spec (.of k))) ⟶ parameter X.hom n := Over.homMk u huover
    have hs : s ≫ F = a := Over.OverMorphism.ext hu
    have hsP : s ≫ (abelMorphism o ho P R n).hom = picardPoint P R
        (classOf X.left L - n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)) := by
      rw [← jacobianAbelMorphism_comp_inclusion hX o ho P R n, ← Category.assoc, hs]
      exact haclass
    let q (index : Fin n) : 𝟙_ (Over (Spec (.of k))) ⟶ X :=
      Over.homMk (s.left ≫ coordinate X.hom n index) (by
        rw [Category.assoc, coordinate_over, Over.w s])
    let E : Divisor X.left := ∑ index : Fin n,
      PointDivisor.pointDivisor X (q index).left (q index).w 1
    have hEeff : ∀ x, 0 ≤ E x := by
      intro x
      dsimp only [E]
      rw [Finsupp.finsetSum_apply]
      exact Finset.sum_nonneg fun index _ =>
        PointDivisor.pointDivisor_nonneg X (q index).left (q index).w 1 x
    have hcoord : s ≫ (abelMorphism o ho P R n).hom = picardPoint P R
        (∑ index : Fin n, (classOf X.left (PointDivisor.positiveLineBundle X hX
          (q index).left (q index).w) -
            classOf X.left (PointDivisor.positiveLineBundle X hX o ho))) := by
      apply parameterPoint_comp_abelMorphism_eq_picardPoint o ho P R s.left s.w
      rw [lineBundle_class_at_point]
      change (PullbackTensor.Local.pullbackHom _) (∑ index : Fin n, _) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun index _ =>
        pointDifference_class_pullback_identity X hX o ho (q index).left (q index).w
    have hc := (picardPoint_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral
      P R).1 (hcoord.symm.trans hsP)
    have hsum : (∑ index : Fin n, classOf X.left (PointDivisor.positiveLineBundle X hX
        (q index).left (q index).w)) = divisorToPicard X.left hd E := by
      dsimp only [E]
      rw [map_sum]
      exact Finset.sum_congr rfl fun index _ =>
        PointDivisor.positiveLineBundle_class_eq_pointDivisor X hX
          (q index).left (q index).w hd
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hc
    rw [hsum] at hc
    have hEclass : divisorToPicard X.left hd E = classOf X.left L := by
      have h := congrArg (fun z : PicardGroup X.left =>
        z + n • classOf X.left (PointDivisor.positiveLineBundle X hX o ho)) hc
      simpa only [sub_add_cancel] using h
    exact (exists_nonzero_section_iff_effective_class X.left hd L).mpr ⟨E, hEeff, hEclass⟩
  · rintro ⟨s, hs⟩
    obtain ⟨u, hu⟩ := exists_comp_abelMorphism_of_nonzero_section hX o ho P R n L hdegree s hs
    have huJ : u ≫ F = a := by
      apply (cancel_mono (identityComponentι P.obj)).mp
      rw [Category.assoc, jacobianAbelMorphism_comp_inclusion]
      exact hu.trans haclass.symm
    exact (F.left.mem_image_iff_exists_lift_spec k a.left).mpr
      ⟨u.left, congrArg Over.Hom.left huJ⟩

end AlgebraicGeometry.Scheme.OverField.Curve.Abel.BoundedFamily
