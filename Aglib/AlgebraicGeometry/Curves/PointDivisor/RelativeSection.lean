/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.PointDivisor.Basic
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Family
public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor.Properties

/-! # The positive class of the original relative section

The actual ideal of a section of a separated smooth relative curve is
invertible. Its dual is the positive section bundle. The canonical relative
Cartier ideal map proves its base-change law, including at arbitrary field
points; the fibre is the existing positive point bundle, not a graph difference.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor

variable {S X T : Scheme.{u}} (p : X ⟶ S)
  [SmoothOfRelativeDimension 1 p] [IsSeparated p]
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

/-- The actual section ideal with its native rank-one theorem. -/
def sectionIdealLineBundle : LineBundle X :=
  ⟨Hom.idealModule o, Hom.sectionIdeal_isLocallyRankOne Hom.smoothRelativeDivisorIdeal p o ho⟩

/-- The positive section bundle is the dual of the original section ideal. -/
def positiveSectionLineBundle : LineBundle X :=
  dualLineBundle X (sectionIdealLineBundle p o ho)

omit [SmoothOfRelativeDimension 1 p] [IsSeparated p] in
/-- The actual pulled-back section is cartesian over the original section. -/
theorem sectionGraph_isPullback (t : T ⟶ S) :
    IsPullback (Hom.graph p t (t ≫ o) (by simp [Category.assoc, ho])) t
      (pullback.fst p t) o := by
  apply IsPullback.of_right (h₁₂ := pullback.snd p t) (h₂₂ := p)
    (v₁₃ := t) _ (Hom.graph_fst p t (t ≫ o) (by simp [Category.assoc, ho]))
      (IsPullback.of_hasPullback p t).flip
  simpa only [Hom.graph_snd, ho] using (IsPullback.of_id_fst (f := t))

/-- Base change of the SAME section ideal through its canonical ideal map. -/
def sectionIdealBaseChangeIso (t : T ⟶ S) :
    (Scheme.Modules.pullback (pullback.fst p t)).obj (sectionIdealLineBundle p o ho).val ≅
      (Hom.graphIdealLineBundle Hom.smoothRelativeDivisorIdeal p t (t ≫ o)
        (by simp [Category.assoc, ho])).val := by
  let s := Hom.graph p t (t ≫ o) (by simp [Category.assoc, ho])
  have h : t ≫ o = s ≫ pullback.fst p t := (Hom.graph_fst p t _ _).symm
  haveI : IsClosedImmersion o := by
    have : IsClosedImmersion (o ≫ p) := by rw [ho]; infer_instance
    exact IsClosedImmersion.of_comp o p
  haveI : Flat (o ≫ p) := by rw [ho]; infer_instance
  have hi : IsIso (Hom.idealPullbackMap o s (pullback.fst p t) t h) :=
    Hom.relativeCartierIdealBaseChange S T X (pullback p t) S T p t
      (pullback.snd p t) (pullback.fst p t) o s t h
      (IsPullback.of_hasPullback p t) (sectionGraph_isPullback p o ho t).flip
      inferInstance (sectionIdealLineBundle p o ho).property inferInstance
  exact @asIso _ _ _ _ (Hom.idealPullbackMap o s (pullback.fst p t) t h) hi

/-- The canonical ideal comparison gives equality of original Picard classes. -/
theorem sectionIdealClass_baseChange (t : T ⟶ S) :
    pullbackClass (pullback.fst p t) (classOf X (sectionIdealLineBundle p o ho)) =
      classOf _ (Hom.graphIdealLineBundle Hom.smoothRelativeDivisorIdeal p t (t ≫ o)
        (by simp [Category.assoc, ho])) := by
  apply Quotient.sound
  exact ⟨sectionIdealBaseChangeIso p o ho t⟩

/-- Positive sign is retained under arbitrary base change. -/
theorem positiveSectionClass_baseChange (t : T ⟶ S) :
    pullbackClass (pullback.fst p t) (classOf X (positiveSectionLineBundle p o ho)) =
      classOf _ (Hom.positiveGraphLineBundle Hom.smoothRelativeDivisorIdeal p t (t ≫ o)
        (by simp [Category.assoc, ho])) := by
  change pullbackClass _ (-classOf X (sectionIdealLineBundle p o ho)) =
    -classOf _ (Hom.graphIdealLineBundle Hom.smoothRelativeDivisorIdeal p t (t ≫ o) _)
  rw [pullbackClass_neg moduleTensorPullback, sectionIdealClass_baseChange]

/-- On a field fibre the positive relative section class is the existing
positive rational-point bundle, with the same lifted section and sign. -/
theorem positiveSectionClass_fieldFibre
    {k : Type u} [Field k] (t : Spec (.of k) ⟶ S)
    (hY : Properties (Over.mk (pullback.snd p t))) :
    pullbackClass (pullback.fst p t) (classOf X (positiveSectionLineBundle p o ho)) =
      classOf _ (positiveLineBundle (Over.mk (pullback.snd p t)) hY
        (Hom.graph p t (t ≫ o) (by simp [Category.assoc, ho]))
        (Hom.graph_snd p t _ _)) := by
  exact positiveSectionClass_baseChange p o ho t

end AlgebraicGeometry.Scheme.OverField.Curve.PointDivisor
