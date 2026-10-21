/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Resolution.NextCenter
public import Aglib.AlgebraicGeometry.Blowup.BaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointShrinking

/-!
Native extraction from the R5 local-model source
`PointedResolution.PointedEtale.Charts`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`4f43d9b68d698fad8dc009c39825e1cd510ea137675f7dddc7fc3bf7ea9a13b6`.
Actual arbitrary-scheme pointed node charts/states, one-step and successor charts, and full
  exceptional-fibre coverage; source Chart/State conditions and all four blowup families are
  retained.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

/-!
# Pointed étale node charts, a single actual blowup step, its successor chart and whole
  exceptional-fibre coverage.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode
universe u

section PointedEtaleNodeChart


/-! A reusable pointed etale node neighbourhood. Both centre squares are full
scheme-theoretic pullbacks. No conclusion about the rest of the global scheme
or any global regularity is part of this structure. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A common etale neighbourhood of a marked point and a power-node origin, with full centre
pullback squares. -/
structure Chart (Y : Scheme.{u}) (π : R) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n) where
  /-- The common neighbourhood scheme mapping etale to both the global scheme and the power node. -/
  C : Scheme.{u}
  /-- The etale map from the common neighbourhood to the global scheme. -/
  toGlobal : C ⟶ Y
  /-- The etale map from the common neighbourhood to the exponent-`n` power node. -/
  toNode : C ⟶ Spec (.of (node π n))
  global_etale : Etale toGlobal
  node_etale : Etale toNode
  /-- The marked residue-field point of the common neighbourhood, lying over both centres. -/
  point : Spec (.of (ResidueField R)) ⟶ C
  /-- The marked residue-field point of the global scheme whose fibre is the common marked point. -/
  globalPoint : Spec (.of (ResidueField R)) ⟶ Y
  globalPoint_closed : IsClosedImmersion globalPoint
  global_square : IsPullback point (𝟙 _) toGlobal globalPoint
  node_square : IsPullback point (𝟙 _) toNode (NextCenter.origin π hπ n hn)

attribute [instance] Chart.global_etale Chart.node_etale Chart.globalPoint_closed

namespace Chart
variable {Y : Scheme.{u}} {π : R} {hπ : Irreducible π} {n : ℕ} {hn : 0 < n}
variable (C : Chart Y π hπ n hn)

@[reassoc (attr := simp)] lemma point_global : C.point ≫ C.toGlobal = C.globalPoint := by
  simpa using C.global_square.w
@[reassoc (attr := simp)] lemma point_node : C.point ≫ C.toNode = NextCenter.origin π hπ n hn := by
  simpa using C.node_square.w

instance point_closed : IsClosedImmersion C.point :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) C.global_square.flip inferInstance

/-- The ideal sheaf cutting out the marked residue-field point in the common neighbourhood. -/
def center : C.C.IdealSheafData := C.point.ker

lemma global_center : C.globalPoint.ker.comap C.toGlobal = C.center := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso C.global_square.isoPullback.hom,
    C.global_square.isoPullback_hom_fst]
  rfl

lemma node_center : (affineCenter (node π n) (centerIdeal π n)).comap C.toNode = C.center := by
  rw [← NextCenter.origin_center π hπ n hn,
    ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso C.node_square.isoPullback.hom,
    C.node_square.isoPullback_hom_fst]
  rfl

lemma center_eq : C.globalPoint.ker.comap C.toGlobal =
    (affineCenter (node π n) (centerIdeal π n)).comap C.toNode :=
  C.global_center.trans C.node_center.symm

instance locallyNoetherian [IsLocallyNoetherian Y] : IsLocallyNoetherian C.C :=
  LocallyOfFiniteType.isLocallyNoetherian C.toGlobal

/-- The ordinary global point blowup, with the actual kernel as centre. -/
def globalBlowup [IsLocallyNoetherian Y] (hex : NoetherianBlowupExistence.{u}) :
    BlowupDatum C.globalPoint.ker := Classical.choice (hex _ _)

/-- Choose the blowup of the common marked-point centre using the supplied Noetherian existence
family. -/
def commonBlowup [IsLocallyNoetherian Y] (hex : NoetherianBlowupExistence.{u}) :
    BlowupDatum C.center := Classical.choice (hex _ _)

lemma globalBlowup_proper [IsLocallyNoetherian Y]
    (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u}) :
    IsProper (C.globalBlowup hex).map := hp _ _ _

end Chart

/-- An actual proper modification of a fixed original scheme, carrying a
pointed common chart and the original residue-point triangle. -/
structure State (X : Scheme.{u}) (q₀ : Spec (.of (ResidueField R)) ⟶ X)
    (π : R) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n) where
  /-- The current source scheme of the proper modification of `X`. -/
  Y : Scheme.{u}
  /-- The proper modification map from the current source scheme to the fixed original scheme `X`.
-/
  map : Y ⟶ X
  proper : IsProper map
  noetherian : IsLocallyNoetherian Y
  /-- The pointed common etale chart on the current source, with exponent `n`. -/
  chart : Chart Y π hπ n hn
  point_triangle : chart.globalPoint ≫ map = q₀

attribute [instance] State.proper State.noetherian
end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end
end PointedEtaleNodeChart

section PointedEtaleBlowupStep


/-! A constructive exponent-reducing step for arbitrary pointed etale node
charts. Every canonical comparison uses the full centre square in the input.
The raw middle chart and its map to the previous common blowup are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y : Scheme.{u}} {π : R} {hπ : Irreducible π} {m : ℕ}
variable (C : Chart Y π hπ (m + 2) (Nat.succ_pos (m + 1)))
  (D : OneStepBlowup.Data π m)
  (BG : BlowupDatum C.globalPoint.ker) (BC : BlowupDatum C.center)

/-- The base-change map from the common-centre blowup to the global marked-point blowup. -/
def toGlobal : BC.Y ⟶ BG.Y := AlgebraicGeometry.Scheme.Blowup.BaseChange.map C.toGlobal
  C.global_center BG BC

/-- The base-change map from the common-centre blowup to the chosen power-node blowup. -/
def toNode : BC.Y ⟶ D.blowup.Y := AlgebraicGeometry.Scheme.Blowup.BaseChange.map C.toNode
  C.node_center D.blowup BC

@[reassoc (attr := simp)] lemma toGlobal_triangle :
    toGlobal C BG BC ≫ BG.map = BC.map ≫ C.toGlobal :=
      AlgebraicGeometry.Scheme.Blowup.BaseChange.map_triangle _ _ _ _
@[reassoc (attr := simp)] lemma toNode_triangle :
    toNode C D BC ≫ D.blowup.map = BC.map ≫ C.toNode :=
      AlgebraicGeometry.Scheme.Blowup.BaseChange.map_triangle _ _ _ _

lemma global_square (hbc : BlowupFlatBaseChange.{u}) :
    IsPullback (toGlobal C BG BC) BC.map BG.map C.toGlobal :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.isPullback hbc _ inferInstance C.global_center BG BC
lemma node_square (hbc : BlowupFlatBaseChange.{u}) :
    IsPullback (toNode C D BC) BC.map D.blowup.map C.toNode :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.isPullback hbc _ inferInstance C.node_center D.blowup
    BC
lemma toGlobal_etale (hbc : BlowupFlatBaseChange.{u}) : Etale (toGlobal C BG BC) :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.etale hbc _ inferInstance C.global_center BG BC
lemma toNode_etale (hbc : BlowupFlatBaseChange.{u}) : Etale (toNode C D BC) :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.etale hbc _ inferInstance C.node_center D.blowup BC

/-- This raw middle exists also at exponent zero, when there is no origin. -/
def middle : Scheme.{u} := pullback (toNode C D BC) (BlowupAtlas.middleChartMap D.atlas hπ)
/-- The projection from the pulled-back middle chart to the common-centre blowup. -/
def middleToCommon : middle C D BC ⟶ BC.Y := pullback.fst _ _
/-- The projection from the pulled-back middle chart to the exponent-reduced node. -/
def middleToNode : middle C D BC ⟶ Spec (.of (node π m)) := pullback.snd _ _
/-- The map from the pulled-back middle chart to the global marked-point blowup. -/
def middleToGlobal : middle C D BC ⟶ BG.Y := middleToCommon C D BC ≫ toGlobal C BG BC

instance middleToCommon_open : IsOpenImmersion (middleToCommon C D BC) := by
  dsimp [middleToCommon]; infer_instance

@[reassoc] lemma middle_square :
    middleToCommon C D BC ≫ toNode C D BC =
      middleToNode C D BC ≫ BlowupAtlas.middleChartMap D.atlas hπ := pullback.condition

lemma middleToNode_etale (hbc : BlowupFlatBaseChange.{u}) : Etale (middleToNode C D BC) := by
  let := toNode_etale C D BC hbc
  dsimp [middleToNode]; infer_instance
lemma middleToGlobal_etale (hbc : BlowupFlatBaseChange.{u}) : Etale (middleToGlobal C D BG BC) := by
  let := toGlobal_etale C BG BC hbc
  dsimp [middleToGlobal]; infer_instance

variable (hm : 0 < m) (hbc : BlowupFlatBaseChange.{u})

/-- The rational point is lifted through the actual cartesian blowup square. -/
def commonPoint : Spec (.of (ResidueField R)) ⟶ BC.Y :=
  (node_square C D BC hbc).lift
    (NextCenter.origin π hπ m hm ≫ BlowupAtlas.middleChartMap D.atlas hπ)
    C.point (by rw [Category.assoc, NextCenter.origin_middleChart_blowdown, C.point_node])

@[reassoc (attr := simp)] lemma commonPoint_node :
    commonPoint C D BC hm hbc ≫ toNode C D BC =
      NextCenter.origin π hπ m hm ≫ BlowupAtlas.middleChartMap D.atlas hπ :=
  (node_square C D BC hbc).lift_fst _ _ _
@[reassoc (attr := simp)] lemma commonPoint_common :
    commonPoint C D BC hm hbc ≫ BC.map = C.point :=
  (node_square C D BC hbc).lift_snd _ _ _

/-- The marked residue-field point in the middle pullback over the exponent-reduced node origin. -/
def middlePoint : Spec (.of (ResidueField R)) ⟶ middle C D BC :=
  pullback.lift (commonPoint C D BC hm hbc) (NextCenter.origin π hπ m hm)
    (commonPoint_node C D BC hm hbc)

@[reassoc (attr := simp)] lemma middlePoint_common :
    middlePoint C D BC hm hbc ≫ middleToCommon C D BC = commonPoint C D BC hm hbc := by
  simp [middlePoint, middleToCommon]
@[reassoc (attr := simp)] lemma middlePoint_node :
    middlePoint C D BC hm hbc ≫ middleToNode C D BC = NextCenter.origin π hπ m hm := by
  simp [middlePoint, middleToNode]

/-- The marked point of the global blowup obtained from the marked middle-chart point. -/
def globalPoint : Spec (.of (ResidueField R)) ⟶ BG.Y :=
  middlePoint C D BC hm hbc ≫ middleToGlobal C D BG BC

@[reassoc (attr := simp)] lemma globalPoint_blowdown :
    globalPoint C D BG BC hm hbc ≫ BG.map = C.globalPoint := by
  simp [globalPoint, middleToGlobal]

instance globalPoint_closed [IsProper BG.map] :
    IsClosedImmersion (globalPoint C D BG BC hm hbc) := by
  have : IsClosedImmersion (globalPoint C D BG BC hm hbc ≫ BG.map) := by
    rw [globalPoint_blowdown]; infer_instance
  exact IsClosedImmersion.of_comp _ BG.map

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step

end
end PointedEtaleBlowupStep

section PointedEtaleSuccessor


/-! Exact full-centre shrinking closes the pointed invariant after each
positive middle exponent. The maps to the raw middle and previous common
chart are retained for later coverage and fibre arguments. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y : Scheme.{u}} {π : R} {hπ : Irreducible π} {m : ℕ}
variable (C : Chart Y π hπ (m + 2) (Nat.succ_pos (m + 1)))
  (D : OneStepBlowup.Data π m)
  (BG : BlowupDatum C.globalPoint.ker) (BC : BlowupDatum C.center)
  (hm : 0 < m) (hbc : BlowupFlatBaseChange.{u}) [IsProper BG.map]

/-- Intersection of the two complements of the unwanted full-fibre pieces. -/
def nextOpen : (middle C D BC).Opens := by
  let := middleToGlobal_etale C D BG BC hbc
  let := middleToNode_etale C D BC hbc
  exact AlgebraicGeometry.Etale.PointShrinking.Common.commonOpen (middlePoint C D BC hm hbc)
    (middleToGlobal C D BG BC) (globalPoint C D BG BC hm hbc) rfl
    (middleToNode C D BC) (NextCenter.origin π hπ m hm) (middlePoint_node C D BC hm hbc)

/-- The invariant closes only after genuine full-fibre shrinking. -/
def nextChart : Chart BG.Y π hπ m hm := by
  let := middleToGlobal_etale C D BG BC hbc
  let := middleToNode_etale C D BC hbc
  let p := middlePoint C D BC hm hbc
  let f := middleToGlobal C D BG BC
  let q := globalPoint C D BG BC hm hbc
  let g := middleToNode C D BC
  let r := NextCenter.origin π hπ m hm
  have h : p ≫ f = q := rfl
  have k : p ≫ g = r := middlePoint_node C D BC hm hbc
  exact {
    C := (AlgebraicGeometry.Etale.PointShrinking.Common.commonOpen p f q h g r k).toScheme
    toGlobal := AlgebraicGeometry.Etale.PointShrinking.Common.toLeft p f q h g r k
    toNode := AlgebraicGeometry.Etale.PointShrinking.Common.toRight p f q h g r k
    global_etale := inferInstance
    node_etale := inferInstance
    point := AlgebraicGeometry.Etale.PointShrinking.Common.point p f q h g r k
    globalPoint := q
    globalPoint_closed := inferInstance
    global_square := AlgebraicGeometry.Etale.PointShrinking.Common.left_isPullback p f q h g r k
    node_square := AlgebraicGeometry.Etale.PointShrinking.Common.right_isPullback p f q h g r k }

/-- Include the next pointed common neighbourhood into the raw middle chart. -/
def nextToMiddle : (nextChart C D BG BC hm hbc).C ⟶ middle C D BC :=
  (nextOpen C D BG BC hm hbc).ι

instance nextToMiddle_open : IsOpenImmersion (nextToMiddle C D BG BC hm hbc) := by
  dsimp [nextToMiddle]; infer_instance

/-- The map from the next pointed common neighbourhood to the common-centre blowup. -/
def nextToCommonBlowup : (nextChart C D BG BC hm hbc).C ⟶ BC.Y :=
  nextToMiddle C D BG BC hm hbc ≫ middleToCommon C D BC

instance nextToCommonBlowup_open : IsOpenImmersion (nextToCommonBlowup C D BG BC hm hbc) := by
  dsimp [nextToCommonBlowup]; infer_instance

/-- The map from the next pointed common neighbourhood back to the previous common neighbourhood. -/
def nextToPrevious : (nextChart C D BG BC hm hbc).C ⟶ C.C :=
  nextToCommonBlowup C D BG BC hm hbc ≫ BC.map

@[reassoc] lemma nextToMiddle_global :
    nextToMiddle C D BG BC hm hbc ≫ middleToGlobal C D BG BC =
      (nextChart C D BG BC hm hbc).toGlobal := rfl
@[reassoc] lemma nextToMiddle_node :
    nextToMiddle C D BG BC hm hbc ≫ middleToNode C D BC =
      (nextChart C D BG BC hm hbc).toNode := rfl

@[reassoc] lemma next_point_middle :
    (nextChart C D BG BC hm hbc).point ≫ nextToMiddle C D BG BC hm hbc =
      middlePoint C D BC hm hbc := by
  let := middleToGlobal_etale C D BG BC hbc
  let := middleToNode_etale C D BC hbc
  exact AlgebraicGeometry.Etale.PointShrinking.Common.point_triangle _ _ _ _ _ _ _

@[reassoc] lemma next_point_previous :
    (nextChart C D BG BC hm hbc).point ≫ nextToPrevious C D BG BC hm hbc = C.point := by
  simp only [nextToPrevious, nextToCommonBlowup, ← Category.assoc,
    next_point_middle, middlePoint_common, commonPoint_common]

@[reassoc] lemma next_global_blowdown :
    (nextChart C D BG BC hm hbc).globalPoint ≫ BG.map = C.globalPoint :=
  globalPoint_blowdown C D BG BC hm hbc

@[reassoc] lemma next_global_triangle :
    (nextChart C D BG BC hm hbc).toGlobal ≫ BG.map =
      nextToPrevious C D BG BC hm hbc ≫ C.toGlobal := by
  rw [← nextToMiddle_global]
  simp only [middleToGlobal, nextToPrevious, nextToCommonBlowup,
    Category.assoc, toGlobal_triangle]

@[reassoc] lemma next_node_triangle :
    (nextChart C D BG BC hm hbc).toNode ≫
      Spec.map (CommRingCat.ofHom (middleBase π m).toRingHom) =
        nextToPrevious C D BG BC hm hbc ≫ C.toNode := by
  rw [← nextToMiddle_node, ← BlowupAtlas.middleChartMap_triangle D.atlas hπ]
  simp only [nextToPrevious, nextToCommonBlowup, Category.assoc]
  rw [← middle_square_assoc, toNode_triangle]

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step

end
end PointedEtaleSuccessor

section PointedExceptionalFibre


/-! The whole exceptional fibre of each actual global blowup is covered by
its same common blowup. This follows from the actual cartesian blowup square
and the literal residue-field point triangle. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {Y : Scheme.{u}} {π : R} {hπ : Irreducible π} {m : ℕ}
variable (C : Chart Y π hπ (m + 2) (Nat.succ_pos (m + 1)))
  (BG : BlowupDatum C.globalPoint.ker) (BC : BlowupDatum C.center)
  (hbc : BlowupFlatBaseChange.{u})

include hbc

lemma exceptional_square :
    IsPullback (pullback.fst BC.map C.point ≫ toGlobal C BG BC)
      (pullback.snd BC.map C.point) BG.map C.globalPoint := by
  simpa only [C.point_global] using
    (IsPullback.of_hasPullback BC.map C.point).paste_horiz (global_square C BG BC hbc)

/-- Identify the exceptional fibre over the common marked point with that over the global marked
point. -/
def exceptionalIso : pullback BC.map C.point ≅ pullback BG.map C.globalPoint :=
  (exceptional_square C BG BC hbc).isoPullback

@[reassoc (attr := simp)] lemma exceptionalIso_hom_fst :
    (exceptionalIso C BG BC hbc).hom ≫ pullback.fst BG.map C.globalPoint =
      pullback.fst BC.map C.point ≫ toGlobal C BG BC :=
  (exceptional_square C BG BC hbc).isoPullback_hom_fst
@[reassoc (attr := simp)] lemma exceptionalIso_hom_snd :
    (exceptionalIso C BG BC hbc).hom ≫ pullback.snd BG.map C.globalPoint =
      pullback.snd BC.map C.point :=
  (exceptional_square C BG BC hbc).isoPullback_hom_snd

/-- Surjectivity over every point above the full original centre, rather
than merely existence of one marked lift. -/
lemma covers_exceptional (z : BG.Y) (hz : BG.map z ∈ Set.range C.globalPoint) :
    z ∈ Set.range (toGlobal C BG BC) := by
  obtain ⟨t, ht⟩ := (AlgebraicGeometry.Scheme.Pullback.range_fst BG.map C.globalPoint).ge hz
  refine ⟨pullback.fst BC.map C.point ((exceptionalIso C BG BC hbc).inv t), ?_⟩
  have H : (exceptionalIso C BG BC hbc).inv ≫
      pullback.fst BC.map C.point ≫ toGlobal C BG BC =
        pullback.fst BG.map C.globalPoint := by
    rw [← exceptionalIso_hom_fst C BG BC hbc, Iso.inv_hom_id_assoc]
  simpa only [Scheme.Hom.comp_apply] using (congrArg (fun f => f t) H).trans ht

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Chart.Step

end
end PointedExceptionalFibre
