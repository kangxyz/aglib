/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.PointedEtale.Charts
public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointShrinkingTop

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.ResolutionGeometry`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`43f3f279e599a901f2de5b7bb01324a0843bf8a6d557dbd09923192f55bef54a`.
Only source602–678: four actual full-middle centre pullback squares and nextOpen_eq_top. No broad
  ResolutionGeometry aggregate is imported.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre

section FullMiddleCentreSquares


/-! The full point-square invariant is stronger than a chosen marked lift.
It proves both raw middle fibres are exactly Spec(k), by actual cartesian
pasting/cancellation. Consequently the constructed successor shrink is top. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y : Scheme.{u}} {π : R} {hπ : Irreducible π} {m : ℕ}
variable (C : Chart Y π hπ (m + 2) (Nat.succ_pos (m + 1))) (D : OneStepBlowup.Data π m)
  (BG : BlowupDatum C.globalPoint.ker) (BC : BlowupDatum C.center)
  (hm : 0 < m) (hbc : BlowupFlatBaseChange.{u})

lemma commonPoint_node_square :
    IsPullback (commonPoint C D BC hm hbc) (𝟙 _) (toNode C D BC)
      (NextCenter.origin π hπ m hm ≫ BlowupAtlas.middleChartMap D.atlas hπ) := by
  have H : IsPullback (commonPoint C D BC hm hbc ≫ BC.map) (𝟙 _)
      C.toNode ((NextCenter.origin π hπ m hm ≫
        BlowupAtlas.middleChartMap D.atlas hπ) ≫ D.blowup.map) := by
    simpa only [commonPoint_common, Category.assoc, NextCenter.origin_middleChart_blowdown] using
      C.node_square
  exact H.of_right (by simp) (node_square C D BC hbc).flip

lemma middlePoint_node_square :
    IsPullback (middlePoint C D BC hm hbc) (𝟙 _) (middleToNode C D BC)
      (NextCenter.origin π hπ m hm) := by
  have H : IsPullback (middlePoint C D BC hm hbc ≫ middleToCommon C D BC) (𝟙 _)
      (toNode C D BC) (NextCenter.origin π hπ m hm ≫ BlowupAtlas.middleChartMap D.atlas hπ) := by
    simpa only [middlePoint_common] using commonPoint_node_square C D BC hm hbc
  exact H.of_right (by simp) (IsPullback.of_hasPullback (toNode C D BC)
    (BlowupAtlas.middleChartMap D.atlas hπ))

lemma commonPoint_global_square :
    IsPullback (commonPoint C D BC hm hbc) (𝟙 _) (toGlobal C BG BC)
      (globalPoint C D BG BC hm hbc) := by
  have H : IsPullback (commonPoint C D BC hm hbc ≫ BC.map) (𝟙 _)
      C.toGlobal (globalPoint C D BG BC hm hbc ≫ BG.map) := by
    simpa only [commonPoint_common, globalPoint_blowdown] using C.global_square
  apply H.of_right _ (global_square C BG BC hbc).flip
  simp only [Category.id_comp, globalPoint, middleToGlobal, ← Category.assoc, middlePoint_common]

lemma middlePoint_global_square :
    IsPullback (middlePoint C D BC hm hbc) (𝟙 _) (middleToGlobal C D BG BC)
      (globalPoint C D BG BC hm hbc) := by
  have H : IsPullback (middlePoint C D BC hm hbc) (𝟙 _)
      (middleToCommon C D BC) (commonPoint C D BC hm hbc) :=
    (IsPullback.of_horiz_isIso_mono
      (show CommSq (𝟙 _) (middlePoint C D BC hm hbc)
        (commonPoint C D BC hm hbc) (middleToCommon C D BC) from ⟨by simp⟩)).flip
  simpa only [Category.id_comp, middleToGlobal] using H.paste_vert (commonPoint_global_square C D
    BG BC hm hbc)

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step


namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y : Scheme.{u}} {π : R} {hπ : Irreducible π} {m : ℕ}
variable (C : Chart Y π hπ (m + 2) (Nat.succ_pos (m + 1))) (D : OneStepBlowup.Data π m)
  (BG : BlowupDatum C.globalPoint.ker) (BC : BlowupDatum C.center)
  (hm : 0 < m) (hbc : BlowupFlatBaseChange.{u}) [IsProper BG.map]

lemma nextOpen_eq_top : nextOpen C D BG BC hm hbc = ⊤ := by
  let := middleToGlobal_etale C D BG BC hbc
  let := middleToNode_etale C D BC hbc
  have hl : AlgebraicGeometry.Etale.PointShrinking.shrinkOpen
      (middlePoint C D BC hm hbc) (middleToGlobal C D BG BC)
      (globalPoint C D BG BC hm hbc) (by rfl) = ⊤ :=
    AlgebraicGeometry.Etale.PointShrinking.shrinkOpen_eq_top _ _ _ _
      (middlePoint_global_square C D BG BC hm hbc)
  have hr : AlgebraicGeometry.Etale.PointShrinking.shrinkOpen
      (middlePoint C D BC hm hbc) (middleToNode C D BC)
      (NextCenter.origin π hπ m hm) (middlePoint_node C D BC hm hbc) = ⊤ :=
    AlgebraicGeometry.Etale.PointShrinking.shrinkOpen_eq_top _ _ _ _
      (middlePoint_node_square C D BC hm hbc)
  exact (congrArg₂ (fun U V : (middle C D BC).Opens => U ⊓ V) hl hr).trans
    (inf_top_eq ⊤)

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step

end -- noncomputable section
end FullMiddleCentreSquares
