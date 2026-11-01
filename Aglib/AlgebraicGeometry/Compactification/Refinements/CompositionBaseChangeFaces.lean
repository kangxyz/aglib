/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionBaseChangeTower
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionBaseChangeRefinement

/-! # Actual first and composite faces of the base-changed dense tower -/

@[expose] public noncomputable section
open CategoryTheory Limits
universe u
namespace AlgebraicGeometry.Scheme.Hom.CompactifiedComposition

variable {X Y Z X' Y' T : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (C : CompactifiedComposition f g)
  (f' : X' ⟶ Y') (g' : Y' ⟶ T) (a : X' ⟶ X) (c : Y' ⟶ Y) (b : T ⟶ Z)
  (sqf : IsPullback a f' f c) (sqg : IsPullback c g' g b)
  [QuasiCompact g]

variable [QuasiCompact f'] [QuasiCompact g']

local notation "D" => cartesianBaseChange C f' g' a c b sqf sqg
local notation "qS" => baseChangeSourceProjection C f' g' a c b sqf sqg
local notation "qT" => baseChangeTargetProjection C g' c b sqg

/-- The proper/open structural maps give the actual first ambient lift. -/
def baseChangeFirstProjection : (D).first.Xbar ⟶ C.first.Xbar :=
  pullback.lift ((D).first.p ≫ c) ((D).middleOpen ≫ qS) (by
    calc
      ((D).first.p ≫ c) ≫ C.targetCompactification.j =
          (D).first.p ≫ (c ≫ C.targetCompactification.j) := Category.assoc _ _ _
      _ = (D).first.p ≫ ((D).targetCompactification.j ≫ qT) :=
        congrArg (fun k => (D).first.p ≫ k)
          (isPullback_baseChangeTarget_open C g' c b sqg).w
      _ = ((D).first.p ≫ (D).targetCompactification.j) ≫ qT :=
        (Category.assoc _ _ _).symm
      _ = ((D).middleOpen ≫ (D).sourceCompactification.p) ≫ qT :=
        congrArg (fun k => k ≫ qT) (D).isPullback_middleOpen.w.symm
      _ = (D).middleOpen ≫ (qS ≫ C.sourceCompactification.p) :=
        (Category.assoc _ _ _).trans (congrArg (fun k => (D).middleOpen ≫ k)
          (baseChangeSourceProjection_p C f' g' a c b sqf sqg).symm)
      _ = ((D).middleOpen ≫ qS) ≫ C.sourceCompactification.p :=
        (Category.assoc _ _ _).symm)

@[reassoc (attr := simp)]
lemma baseChangeFirstProjection_p :
    baseChangeFirstProjection C f' g' a c b sqf sqg ≫ C.first.p = (D).first.p ≫ c :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChangeFirstProjection_middleOpen :
    baseChangeFirstProjection C f' g' a c b sqf sqg ≫ C.middleOpen = (D).middleOpen ≫ qS :=
  pullback.lift_snd _ _ _

/-- The middle-open face is Cartesian by actual pullback cancellation. -/
lemma isPullback_baseChangeMiddleOpen :
    IsPullback (baseChangeFirstProjection C f' g' a c b sqf sqg)
      (D).middleOpen C.middleOpen qS := by
  have hout := (D).isPullback_middleOpen.flip.paste_horiz
    (isPullback_baseChangeTarget_open C g' c b sqg)
  rw [← baseChangeFirstProjection_p, ← baseChangeSourceProjection_p] at hout
  exact hout.of_right (baseChangeFirstProjection_middleOpen C f' g' a c b sqf sqg)
    C.isPullback_middleOpen.flip

/-- The first ambient lift retains the original open source. -/
@[reassoc]
lemma first_j_baseChangeFirstProjection :
    (D).first.j ≫ baseChangeFirstProjection C f' g' a c b sqf sqg = a ≫ C.first.j := by
  apply (cancel_mono C.middleOpen).mp
  rw [Category.assoc, baseChangeFirstProjection_middleOpen, ← Category.assoc,
    first_j_middleOpen, Category.assoc, first_j_middleOpen]
  exact (isPullback_baseChangeSource_open C f' g' a c b sqf sqg).w.symm

/-- The actual first ambient map is Cartesian over the original open source. -/
lemma isPullback_baseChangeFirst_open :
    IsPullback a (D).first.j C.first.j
      (baseChangeFirstProjection C f' g' a c b sqf sqg) :=
  Compactification.isPullback_cartesianRefinement_open C.first.toCompactification
    f' a c sqf (D).first (baseChangeFirstProjection C f' g' a c b sqf sqg)
    (first_j_baseChangeFirstProjection C f' g' a c b sqf sqg)
    (baseChangeFirstProjection_p C f' g' a c b sqf sqg)

/-- The first model has an actual refinement to the normalized original base change. -/
def baseChangeFirstRefinement : (D).first ⟶
    Compactification.normalizedCartesianBaseChange C.first.toCompactification f' a c sqf :=
  Compactification.normalizedCartesianRefinement C.first.toCompactification f' a c sqf
    (D).first (baseChangeFirstProjection C f' g' a c b sqf sqg)
    (first_j_baseChangeFirstProjection C f' g' a c b sqf sqg)
    (baseChangeFirstProjection_p C f' g' a c b sqf sqg)

omit [QuasiCompact g] in
/-- The same actual source map respects both composite proper structural maps. -/
@[reassoc]
lemma baseChangeSourceProjection_composite_p :
    qS ≫ C.composite.p = (D).composite.p ≫ b := by
  change qS ≫ (C.sourceCompactification.p ≫ C.targetCompactification.p) =
    ((D).sourceCompactification.p ≫ (D).targetCompactification.p) ≫ b
  rw [← Category.assoc, baseChangeSourceProjection_p, Category.assoc]
  exact (congrArg (fun k => (D).sourceCompactification.p ≫ k)
    (Compactification.cartesianBaseChangeProjection_p
      C.targetCompactification.toCompactification g' c b sqg)).trans
        (Category.assoc _ _ _).symm

/-- The composite model refines the normalized base change of the original composite. -/
def baseChangeCompositeRefinement : (D).composite ⟶
    Compactification.normalizedCartesianBaseChange C.composite.toCompactification
      (f' ≫ g') a b (sqf.paste_vert sqg) :=
  Compactification.normalizedCartesianRefinement C.composite.toCompactification
    (f' ≫ g') a b (sqf.paste_vert sqg) (D).composite qS
    (isPullback_baseChangeSource_open C f' g' a c b sqf sqg).w.symm
    (baseChangeSourceProjection_composite_p C f' g' a c b sqf sqg)

end AlgebraicGeometry.Scheme.Hom.CompactifiedComposition
