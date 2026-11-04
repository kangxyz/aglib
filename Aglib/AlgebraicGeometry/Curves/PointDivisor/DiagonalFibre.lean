/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.PointDivisor.RelativeSection

/-! The original diagonal under the original section of a curve. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor

universe u

variable {X S : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

/-- The original product restricted along a rational section uses the same curve. -/
def diagonalSectionFibreMap : X ⟶ pullback p p :=
  pullback.lift (𝟙 X) (p ≫ o) (by simp [Category.assoc, ho])

theorem diagonalSectionFibreMap_isPullback :
    IsPullback (diagonalSectionFibreMap p o ho) p (pullback.snd p p) o := by
  let j := diagonalSectionFibreMap p o ho
  have hf : j ≫ pullback.fst p p = 𝟙 X := pullback.lift_fst _ _ _
  have hs : j ≫ pullback.snd p p = p ≫ o := pullback.lift_snd _ _ _
  have h : IsPullback (j ≫ pullback.fst p p) p p (o ≫ p) := by
    rw [hf, ho]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact IsPullback.of_right h hs (IsPullback.of_hasPullback p p)

/-- The same pullback restricts the original diagonal section to the original point. -/
theorem diagonalSectionFibreMap_diagonal_isPullback :
    IsPullback o o (pullback.diagonal p) (diagonalSectionFibreMap p o ho) := by
  let j := diagonalSectionFibreMap p o ho
  have hf : j ≫ pullback.fst p p = 𝟙 X := pullback.lift_fst _ _ _
  have hs : j ≫ pullback.snd p p = p ≫ o := pullback.lift_snd _ _ _
  have hc : o ≫ pullback.diagonal p = o ≫ j := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, hf, Category.comp_id]
    · simp only [Category.assoc, pullback.diagonal_snd, hs, Category.comp_id]
      rw [← Category.assoc, ho, Category.id_comp]
  have h : IsPullback (o ≫ p) o o (pullback.diagonal p ≫ pullback.snd p p) := by
    rw [ho, pullback.diagonal_snd]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact (IsPullback.of_right h hc.symm (diagonalSectionFibreMap_isPullback p o ho).flip).flip

open Scheme.Modules.Invertible

variable [SmoothOfRelativeDimension 1 p] [IsSeparated p]

/-- The original diagonal ideal pulls back to the original section ideal. -/
theorem diagonalIdealClass_pullback_sectionFibre :
    pullbackClass (diagonalSectionFibreMap p o ho)
      (classOf _ (Hom.diagonalIdealLineBundle Hom.smoothRelativeDivisorIdeal p)) =
        classOf X (sectionIdealLineBundle p o ho) := by
  let j := diagonalSectionFibreMap p o ho
  let i := pullback.diagonal p
  have hbase := diagonalSectionFibreMap_isPullback p o ho
  have hsection := diagonalSectionFibreMap_diagonal_isPullback p o ho
  have hr : IsLocallyRankOne (pullback p p) (Hom.idealModule i) :=
    (Hom.diagonalIdealLineBundle Hom.smoothRelativeDivisorIdeal p).property
  have hf : Flat (i ≫ pullback.snd p p) := by dsimp [i]; rw [pullback.diagonal_snd]; infer_instance
  have hi : IsIso (Hom.idealPullbackMap i o j o hsection.w) :=
    Hom.relativeCartierIdealBaseChange X S (pullback p p) X X S
      (pullback.snd p p) o p j i o o hsection.w hbase hsection inferInstance hr hf
  -- Use the same original ideal map.
  apply Quotient.sound
  exact ⟨@asIso _ _ _ _ (Hom.idealPullbackMap i o j o hsection.w) hi⟩

/-- The original universal Abel class is the positive diagonal class
minus the first projection pullback of the original origin class. -/
theorem abelClass_identity_eq_diagonal_sub_origin :
    Hom.abelClass Hom.smoothRelativeDivisorIdeal p o ho p (𝟙 X) (Category.id_comp p) =
      -classOf _ (Hom.diagonalIdealLineBundle Hom.smoothRelativeDivisorIdeal p) -
        pullbackClass (pullback.fst p p) (classOf X (positiveSectionLineBundle p o ho)) := by
  have h : pullbackClass (pullback.fst p p) (classOf X (positiveSectionLineBundle p o ho)) =
      -classOf _ (Hom.originIdealLineBundle Hom.smoothRelativeDivisorIdeal p o ho p) :=
    positiveSectionClass_baseChange p o ho p
  rw [Hom.abelClass_eq, h, sub_neg_eq_add]
  rfl


end AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor
