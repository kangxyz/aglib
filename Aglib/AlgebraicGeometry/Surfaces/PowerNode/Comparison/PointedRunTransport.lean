/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Gluing.SourceOpenCover
public import Aglib.AlgebraicGeometry.Limits.Range
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.PointedEtale.Runs
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.PointedEtale.FullMiddleCenters
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Resolution.Recursion
public import Aglib.AlgebraicGeometry.Morphisms.IsIso.OpenPullback

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.PointedRunTransport`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`b9c4c8afd6655b96e117a053e59a6b8d1913e36737ad338bd3eab0dbc5614734`.
Actual node/pointed scheme maps, full covers, original structural triangles and source quantifiers
  are retained. Universal blowup inputs remain conditional.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre

/-!
# Retained pointed-run charts, comparison maps, and source-open gluing

This module preserves the conditional interfaces and source-coverage boundaries
recorded in the individual sections below.
-/

section PointedRunRelativeUnchanged

/-! Retention of the entire complement of the CURRENT centre for every actual
finite Run. The auxiliary statement allows any actual map carrying that centre
to a fixed residue point. In particular it does not discard earlier exceptional
pieces merely because they contract to the original residue point. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π}

lemma State.center_disjoint_relative {n : ℕ} {hn : 0 < n}
    (S : State X q₀ π hπ n hn) {B : Scheme.{u}}
    (b : S.Y ⟶ B) (q : Spec (.of (ResidueField R)) ⟶ B)
    (hb : S.chart.globalPoint ≫ b = q) (U : B.Opens)
    (hU : Disjoint (U : Set B) (Set.range q)) :
    Disjoint ((b ⁻¹ᵁ U) : Set S.Y) (S.chart.globalPoint.ker.support : Set S.Y) := by
  rw [Scheme.Hom.support_ker, S.chart.globalPoint.isClosedEmbedding.isClosed_range.closure_eq]
  apply Set.disjoint_left.mpr
  rintro z hz ⟨w, rfl⟩
  apply Set.disjoint_left.mp hU hz
  exact ⟨w, (congrArg (fun f => f w) hb).symm⟩

namespace Run
variable {hex : NoetherianBlowupExistence.{u}} {hp : NoetherianBlowupProper.{u}}
  {hatlas : BlowupAffineAtlas.{u}} {hbc : BlowupFlatBaseChange.{u}}

lemma relative_unchanged : {n : ℕ} → {hn : 0 < n} →
    {S : State X q₀ π hπ n hn} → (T : Run hex hp hatlas hbc S) →
    {B : Scheme.{u}} → (b : S.Y ⟶ B) → (q : Spec (.of (ResidueField R)) ⟶ B) →
    S.chart.globalPoint ≫ b = q → (U : B.Opens) →
    Disjoint (U : Set B) (Set.range q) → IsIso (b ∣_ U) →
    IsIso ((T.map ≫ b) ∣_ U)
  | _, _, _, .one S, _, b, _, _, U, _, hb => by
      change IsIso ((𝟙 S.Y ≫ b) ∣_ U)
      rw [Category.id_comp]
      exact hb
  | _, _, _, .two S, _, b, q, hq, U, hU, hb => by
      let := hb
      let := (S.blowup hex).restrict_isIso_of_disjoint (b ⁻¹ᵁ U)
        (S.center_disjoint_relative b q hq U hU)
      exact Scheme.Hom.isIso_restrict_comp (S.blowup hex).map b U
  | _, _, _, .next m S tail, _, b, q, hq, U, hU, hb => by
      let := hb
      let := (S.blowup hex).restrict_isIso_of_disjoint (b ⁻¹ᵁ U)
        (S.center_disjoint_relative b q hq U hU)
      have hs : IsIso (((S.blowup hex).map ≫ b) ∣_ U) :=
        Scheme.Hom.isIso_restrict_comp _ _ U
      have hq' : (S.step hex hp hatlas hbc (Nat.succ_pos m)).chart.globalPoint ≫
          ((S.blowup hex).map ≫ b) = q := by
        let := S.blowup_proper hex hp
        change Chart.Step.globalPoint S.chart
          (OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas)
          (S.blowup hex) (S.commonBlowup hex) (by omega) hbc ≫
          ((S.blowup hex).map ≫ b) = q
        rw [← Category.assoc, Chart.Step.globalPoint_blowdown]
        exact hq
      change IsIso (((tail.map ≫ (S.blowup hex).map) ≫ b) ∣_ U)
      rw [Category.assoc]
      exact relative_unchanged tail ((S.blowup hex).map ≫ b) q hq' U hU hs

variable {n : ℕ} {hn : 0 < n} {S : State X q₀ π hπ n hn}
  (T : Run hex hp hatlas hbc S)

/-- Every later blowup is an isomorphism over the complement of this State's
actual centre, including earlier exceptional pieces lying in that complement. -/
lemma map_unchanged (U : S.Y.Opens)
    (hU : Disjoint (U : Set S.Y) (Set.range S.chart.globalPoint)) :
    IsIso (T.map ∣_ U) := by
  have h := relative_unchanged T (𝟙 S.Y) S.chart.globalPoint (by simp) U hU
    (show IsIso ((𝟙 S.Y) ∣_ U) by infer_instance)
  rw [Category.comp_id] at h
  exact h

/-- Identify the inverse image of an open disjoint from the current marked point with that open. -/
def currentOpenIso (U : S.Y.Opens)
    (hU : Disjoint (U : Set S.Y) (Set.range S.chart.globalPoint)) :
    (T.map ⁻¹ᵁ U).toScheme ≅ U.toScheme := by
  letI := map_unchanged T U hU
  exact asIso (T.map ∣_ U)

@[reassoc] lemma currentOpenIso_triangle (U : S.Y.Opens)
    (hU : Disjoint (U : Set S.Y) (Set.range S.chart.globalPoint)) :
    (currentOpenIso T U hU).hom ≫ U.ι = (T.map ⁻¹ᵁ U).ι ≫ T.map :=
  morphismRestrict_ι _ _

/-- A retained actual component or branch portion lifts uniquely when its map
lands in the unchanged current-centre complement. -/
lemma current_pullback_isIso {A : Scheme.{u}} (j : A ⟶ S.Y) (U : S.Y.Opens)
    (hU : Disjoint (U : Set S.Y) (Set.range S.chart.globalPoint))
    (hj : Set.range j ⊆ U) : IsIso (pullback.snd T.map j) := by
  let := map_unchanged T U hU
  exact Scheme.Hom.isIso_pullback_of_range_subset T.map U j hj

end Run
end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end PointedRunRelativeUnchanged


section PointedRunFullCommon

/-! The full common base change of the actual finite Run, distinct from its
terminal middle chart. Its residue fibre is exactly the full global exceptional
fibre. At a successor it is also the pullback of the ENTIRE tail along the
previous common blowup, retaining both earlier outer pieces and the middle. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π}
  {hex : NoetherianBlowupExistence.{u}} {hp : NoetherianBlowupProper.{u}}
  {hatlas : BlowupAffineAtlas.{u}} {hbc : BlowupFlatBaseChange.{u}}
  {n : ℕ} {hn : 0 < n} {S : State X q₀ π hπ n hn}
  (T : Run hex hp hatlas hbc S)

/-- All of the actual Run over the original common chart, not merely the last
middle chart. -/
def fullCommon : Scheme.{u} := pullback T.map S.chart.toGlobal

/-- The projection from the full common pullback to the final source of the run. -/
def fullCommonToGlobal : fullCommon T ⟶ T.source := pullback.fst _ _
/-- The projection from the full common pullback to the starting common chart. -/
def fullCommonMap : fullCommon T ⟶ S.chart.C := pullback.snd _ _

lemma fullCommon_square :
    IsPullback (fullCommonToGlobal T) (fullCommonMap T) T.map S.chart.toGlobal :=
  IsPullback.of_hasPullback _ _

@[reassoc (attr := simp)] lemma fullCommon_triangle :
    fullCommonToGlobal T ≫ T.map = fullCommonMap T ≫ S.chart.toGlobal :=
  pullback.condition

/-- The residue-point square remains cartesian for the ENTIRE arbitrary Run. -/
lemma fullCommon_exceptional_square :
    IsPullback (pullback.fst (fullCommonMap T) S.chart.point ≫ fullCommonToGlobal T)
      (pullback.snd (fullCommonMap T) S.chart.point) T.map S.chart.globalPoint := by
  simpa only [S.chart.point_global] using
    (IsPullback.of_hasPullback (fullCommonMap T) S.chart.point).paste_horiz
      (fullCommon_square T)

/-- This is an isomorphism of the actual full fibres, over the literal original
residue field. It does not yet compare to the independently glued node model. -/
def fullCommonExceptionalIso : pullback (fullCommonMap T) S.chart.point ≅
    pullback T.map S.chart.globalPoint := (fullCommon_exceptional_square T).isoPullback

@[reassoc (attr := simp)] lemma fullCommonExceptionalIso_hom_fst :
    (fullCommonExceptionalIso T).hom ≫ pullback.fst T.map S.chart.globalPoint =
      pullback.fst (fullCommonMap T) S.chart.point ≫ fullCommonToGlobal T :=
  (fullCommon_exceptional_square T).isoPullback_hom_fst

@[reassoc (attr := simp)] lemma fullCommonExceptionalIso_hom_snd :
    (fullCommonExceptionalIso T).hom ≫ pullback.snd T.map S.chart.globalPoint =
      pullback.snd (fullCommonMap T) S.chart.point :=
  (fullCommon_exceptional_square T).isoPullback_hom_snd

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run

namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run.Step
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π} {m : ℕ}
  (S : State X q₀ π hπ (m + 3) (Nat.succ_pos (m + 2)))
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (tail : Run hex hp hatlas hbc (S.step hex hp hatlas hbc (Nat.succ_pos m)))

/-- The full tail over the preceding common blowup. -/
def retainedCommon : Scheme.{u} :=
  pullback tail.map (Chart.Step.toGlobal S.chart (S.blowup hex) (S.commonBlowup hex))

/-- The projection from the common blowup retained through the tail run to the tail source. -/
def retainedToGlobal : retainedCommon S hex hp hatlas hbc tail ⟶ tail.source :=
  pullback.fst _ _
/-- The projection from the retained common pullback to the current common blowup. -/
def retainedToBlowup : retainedCommon S hex hp hatlas hbc tail ⟶ (S.commonBlowup hex).Y :=
  pullback.snd _ _

lemma retained_square :
    IsPullback (retainedToGlobal S hex hp hatlas hbc tail)
      (retainedToBlowup S hex hp hatlas hbc tail) tail.map
      (Chart.Step.toGlobal S.chart (S.blowup hex) (S.commonBlowup hex)) :=
  IsPullback.of_hasPullback _ _

lemma retained_original_square :
    IsPullback (retainedToGlobal S hex hp hatlas hbc tail)
      (retainedToBlowup S hex hp hatlas hbc tail ≫ (S.commonBlowup hex).map)
      (Run.next m S tail).map S.chart.toGlobal := by
  exact (retained_square S hex hp hatlas hbc tail).paste_vert
    (Chart.Step.global_square S.chart (S.blowup hex) (S.commonBlowup hex) hbc)

/-- The retained source is exactly the common base change of the same Run.next. -/
def retainedFullCommonIso : retainedCommon S hex hp hatlas hbc tail ≅
    (Run.next m S tail).fullCommon :=
  (retained_original_square S hex hp hatlas hbc tail).isoPullback

@[reassoc (attr := simp)] lemma retainedFullCommonIso_hom_global :
    (retainedFullCommonIso S hex hp hatlas hbc tail).hom ≫
      (Run.next m S tail).fullCommonToGlobal = retainedToGlobal S hex hp hatlas hbc tail :=
  (retained_original_square S hex hp hatlas hbc tail).isoPullback_hom_fst

@[reassoc (attr := simp)] lemma retainedFullCommonIso_hom_chart :
    (retainedFullCommonIso S hex hp hatlas hbc tail).hom ≫
      (Run.next m S tail).fullCommonMap =
      retainedToBlowup S hex hp hatlas hbc tail ≫ (S.commonBlowup hex).map :=
  (retained_original_square S hex hp hatlas hbc tail).isoPullback_hom_snd

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run.Step

end -- noncomputable section
end PointedRunFullCommon


section PointedRunRetainedCover

/-! A recursive open cover of the ENTIRE common base change of Run.next.
The middle chart is exactly the full common base change of the tail; the outer
chart is retained in addition. All maps are literal pullback projections, and
the successor shrink is identified with the whole raw middle using the proved
full-centre squares. No cover by the terminal Run.common is asserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run.Step
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π} {m : ℕ}
  (S : State X q₀ π hπ (m + 3) (Nat.succ_pos (m + 2)))
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (tail : Run hex hp hatlas hbc (S.step hex hp hatlas hbc (Nat.succ_pos m)))

/-- Include the next pointed common chart into the raw middle chart before shrinking. -/
def currentMiddleToRaw : (S.step hex hp hatlas hbc (Nat.succ_pos m)).chart.C ⟶
    Chart.Step.middle S.chart (OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas)
      (S.commonBlowup hex) := by
  letI := S.blowup_proper hex hp
  exact Chart.Step.nextToMiddle S.chart (OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas)
    (S.blowup hex) (S.commonBlowup hex) (by omega) hbc

/-- The map from the next pointed common chart to the current common blowup through the middle
chart. -/
def currentMiddleMap : (S.step hex hp hatlas hbc (Nat.succ_pos m)).chart.C ⟶
    (S.commonBlowup hex).Y :=
  currentMiddleToRaw S hex hp hatlas hbc ≫
    Chart.Step.middleToCommon S.chart (OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas)
      (S.commonBlowup hex)

instance currentMiddleMap_open : IsOpenImmersion (currentMiddleMap S hex hp hatlas hbc) := by
  let := S.blowup_proper hex hp
  dsimp [currentMiddleMap, currentMiddleToRaw]; infer_instance

@[reassoc] lemma currentMiddleMap_global :
    currentMiddleMap S hex hp hatlas hbc ≫
      Chart.Step.toGlobal S.chart (S.blowup hex) (S.commonBlowup hex) =
      (S.step hex hp hatlas hbc (Nat.succ_pos m)).chart.toGlobal := by
  let := S.blowup_proper hex hp
  simp only [currentMiddleMap, currentMiddleToRaw, Category.assoc]
  rfl

lemma nextToMiddle_isIso : IsIso (currentMiddleToRaw S hex hp hatlas hbc) := by
  let := S.blowup_proper hex hp
  let : IsOpenImmersion (currentMiddleToRaw S hex hp hatlas hbc) := by
    dsimp [currentMiddleToRaw]
    infer_instance
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top (currentMiddleToRaw S hex hp hatlas hbc)
  exact (Scheme.Opens.opensRange_ι _).trans
    (Chart.Step.nextOpen_eq_top S.chart
      (OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas)
      (S.blowup hex) (S.commonBlowup hex) (by omega) hbc)

lemma currentMiddleMap_range : Set.range (currentMiddleMap S hex hp hatlas hbc) =
    (Chart.Step.toNode S.chart (OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas) (S.commonBlowup
      hex)) ⁻¹'
      Set.range (BlowupAtlas.middleChartMap (OneStepBlowup.ofFamilies π (m + 1) hex hp
        hatlas).atlas hπ) := by
  let := nextToMiddle_isIso S hex hp hatlas hbc
  change Set.range ((Chart.Step.middleToCommon S.chart (OneStepBlowup.ofFamilies π (m + 1) hex hp
    hatlas)
    (S.commonBlowup hex)) ∘ (currentMiddleToRaw S hex hp hatlas hbc)) = _
  have hs : Function.Surjective (currentMiddleToRaw S hex hp hatlas hbc) :=
    (currentMiddleToRaw S hex hp hatlas hbc).homeomorph.surjective
  rw [hs.range_comp]
  exact Scheme.Pullback.range_fst _ _

/-- The inverse image of the node blowup outer open in the current common blowup. -/
def currentOuterOpen : (S.commonBlowup hex).Y.Opens :=
  Chart.Step.toNode S.chart (OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas) (S.commonBlowup
    hex) ⁻¹ᵁ
    Resolution.outerOpen (OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas) hπ

lemma currentMiddle_outer_cover :
    (currentMiddleMap S hex hp hatlas hbc).opensRange ⊔ currentOuterOpen S hex hp hatlas = ⊤ := by
  apply top_le_iff.mp
  intro z _
  have hz : Chart.Step.toNode S.chart (OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas)
    (S.commonBlowup hex) z ∈
      (BlowupAtlas.middleChartMap (OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas).atlas
        hπ).opensRange ⊔
        Resolution.outerOpen (OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas) hπ := by
    rw [Resolution.middle_outer_cover]
    trivial
  rcases hz with hz | hz
  · left
    change z ∈ Set.range (currentMiddleMap S hex hp hatlas hbc)
    rw [currentMiddleMap_range]
    exact hz
  · exact Or.inr hz

/-- The exact recursive middle piece in the full retained source. -/
def retainedMiddle : Scheme.{u} :=
  pullback (retainedToBlowup S hex hp hatlas hbc tail) (currentMiddleMap S hex hp hatlas hbc)

/-- Include the retained middle piece into the common blowup pullback retained through the tail. -/
def retainedMiddleInclusion : retainedMiddle S hex hp hatlas hbc tail ⟶
    retainedCommon S hex hp hatlas hbc tail := pullback.fst _ _

instance retainedMiddleInclusion_open :
    IsOpenImmersion (retainedMiddleInclusion S hex hp hatlas hbc tail) := by
  dsimp [retainedMiddleInclusion]; infer_instance

lemma retainedMiddle_square :
    IsPullback (retainedMiddleInclusion S hex hp hatlas hbc tail ≫
      retainedToGlobal S hex hp hatlas hbc tail)
      (pullback.snd (retainedToBlowup S hex hp hatlas hbc tail)
        (currentMiddleMap S hex hp hatlas hbc)) tail.map
      (S.step hex hp hatlas hbc (Nat.succ_pos m)).chart.toGlobal := by
  simpa only [currentMiddleMap_global, retainedMiddleInclusion, retainedMiddle] using
    (IsPullback.of_hasPullback (retainedToBlowup S hex hp hatlas hbc tail)
      (currentMiddleMap S hex hp hatlas hbc)).paste_horiz
        (retained_square S hex hp hatlas hbc tail)

/-- The recursive piece is the ENTIRE common base change of the actual tail. -/
def retainedMiddleIso : retainedMiddle S hex hp hatlas hbc tail ≅ tail.fullCommon :=
  (retainedMiddle_square S hex hp hatlas hbc tail).isoPullback

@[reassoc (attr := simp)] lemma retainedMiddleIso_hom_global :
    (retainedMiddleIso S hex hp hatlas hbc tail).hom ≫ tail.fullCommonToGlobal =
      retainedMiddleInclusion S hex hp hatlas hbc tail ≫
        retainedToGlobal S hex hp hatlas hbc tail :=
  (retainedMiddle_square S hex hp hatlas hbc tail).isoPullback_hom_fst

@[reassoc (attr := simp)] lemma retainedMiddleIso_hom_chart :
    (retainedMiddleIso S hex hp hatlas hbc tail).hom ≫ tail.fullCommonMap =
      pullback.snd (retainedToBlowup S hex hp hatlas hbc tail)
        (currentMiddleMap S hex hp hatlas hbc) :=
  (retainedMiddle_square S hex hp hatlas hbc tail).isoPullback_hom_snd

/-- Retain the entire outer piece in addition to the recursive middle. -/
def retainedOuter : Scheme.{u} :=
  pullback (retainedToBlowup S hex hp hatlas hbc tail) (currentOuterOpen S hex hp hatlas).ι

/-- Include the retained outer piece into the common blowup pullback retained through the tail. -/
def retainedOuterInclusion : retainedOuter S hex hp hatlas hbc tail ⟶
    retainedCommon S hex hp hatlas hbc tail := pullback.fst _ _

instance retainedOuterInclusion_open :
    IsOpenImmersion (retainedOuterInclusion S hex hp hatlas hbc tail) := by
  dsimp [retainedOuterInclusion]; infer_instance

lemma retained_charts_cover (z : retainedCommon S hex hp hatlas hbc tail) :
    z ∈ Set.range (retainedMiddleInclusion S hex hp hatlas hbc tail) ∨
      z ∈ Set.range (retainedOuterInclusion S hex hp hatlas hbc tail) := by
  have hz : retainedToBlowup S hex hp hatlas hbc tail z ∈
      (currentMiddleMap S hex hp hatlas hbc).opensRange ⊔ currentOuterOpen S hex hp hatlas := by
    rw [currentMiddle_outer_cover]
    trivial
  rcases hz with hz | hz
  · left
    change z ∈ Set.range (pullback.fst (retainedToBlowup S hex hp hatlas hbc tail)
      (currentMiddleMap S hex hp hatlas hbc))
    rw [Scheme.Pullback.range_fst]
    exact hz
  · right
    change z ∈ Set.range (pullback.fst (retainedToBlowup S hex hp hatlas hbc tail)
      (currentOuterOpen S hex hp hatlas).ι)
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    exact hz

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run.Step

end -- noncomputable section
end PointedRunRetainedCover


section PointedRunRetainedMorphisms

/-! Canonical lifts of unchanged actual component and branch morphisms through
an arbitrary tail, preserving their source schemes and scheme intersections.
The condition is disjointness from the CURRENT centre, proved separately for
the actual outer pieces. No component scheme or intersection is supplied as a
replacement for a geometric calculation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π}
  {hex : NoetherianBlowupExistence.{u}} {hp : NoetherianBlowupProper.{u}}
  {hatlas : BlowupAffineAtlas.{u}} {hbc : BlowupFlatBaseChange.{u}}
  {n : ℕ} {hn : 0 < n} {S : State X q₀ π hπ n hn}
  (T : Run hex hp hatlas hbc S)

/-- The open complement of the current marked residue-field point in the state source. -/
def currentComplement : S.Y.Opens :=
  ⟨(Set.range S.chart.globalPoint)ᶜ,
    S.chart.globalPoint.isClosedEmbedding.isClosed_range.isOpen_compl⟩

lemma currentComplement_disjoint :
    Disjoint (currentComplement (S := S) : Set S.Y) (Set.range S.chart.globalPoint) :=
  by
    apply Set.disjoint_left.mpr
    intro z hz hq
    exact hz hq

variable {A : Scheme.{u}} (j : A ⟶ S.Y)
  (hj : Disjoint (Set.range j) (Set.range S.chart.globalPoint))

include hj in
lemma retained_projection_isIso : IsIso (pullback.snd T.map j) := by
  apply current_pullback_isIso T j (currentComplement (S := S)) currentComplement_disjoint
  intro a ha
  exact fun hq => Set.disjoint_left.mp hj ha hq

/-- The original source scheme is unchanged; only its actual map is lifted. -/
def retainedMap : A ⟶ T.source := by
  letI := retained_projection_isIso T j hj
  exact inv (pullback.snd T.map j) ≫ pullback.fst T.map j

@[reassoc (attr := simp)] lemma retainedMap_triangle :
    retainedMap T j hj ≫ T.map = j := by
  let := retained_projection_isIso T j hj
  simp only [retainedMap, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

/-- Retention is a full scheme-theoretic base change, rather than equality of
images or points. -/
lemma retainedMap_square : IsPullback (retainedMap T j hj) (𝟙 A) T.map j := by
  let := retained_projection_isIso T j hj
  exact (IsPullback.of_hasPullback T.map j).of_iso
    (asIso (pullback.snd T.map j)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [retainedMap]) (by simp) (by simp) (by simp)

instance retainedMap_closed [IsClosedImmersion j] : IsClosedImmersion (retainedMap T j hj) := by
  let := retained_projection_isIso T j hj
  dsimp [retainedMap]
  infer_instance

/-- The cartesian lift is uniquely determined by the same contraction triangle. -/
lemma retainedMap_unique {P : Scheme.{u}} (f : P ⟶ T.source) (s : P ⟶ A)
    (H : f ≫ T.map = s ≫ j) : s ≫ retainedMap T j hj = f := by
  have h := (retainedMap_square T j hj).lift_snd f s H
  simp only [Category.comp_id] at h
  simpa only [h] using (retainedMap_square T j hj).lift_fst f s H

variable {B P : Scheme.{u}} (g : B ⟶ S.Y)
  (hg : Disjoint (Set.range g) (Set.range S.chart.globalPoint))
  (s : P ⟶ A) (t : P ⟶ B)

/-- Both original attachment maps are unchanged when both participating pieces
avoid the current centre. This applies to every later tail blowup. -/
lemma retainedMaps_isPullback (H : IsPullback s t j g) :
    IsPullback s t (retainedMap T j hj) (retainedMap T g hg) := by
  have hw : s ≫ retainedMap T j hj = t ≫ retainedMap T g hg := by
    apply retainedMap_unique T j hj (t ≫ retainedMap T g hg) s
    simpa only [Category.assoc, retainedMap_triangle] using H.w.symm
  have hh : IsPullback (s ≫ 𝟙 A) t j (retainedMap T g hg ≫ T.map) := by
    simpa only [Category.comp_id, retainedMap_triangle] using H
  exact hh.of_right hw (retainedMap_square T j hj).flip

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run

end -- noncomputable section
end PointedRunRetainedMorphisms


section PointedRunOuterRetention

/-! The actual outer source avoids the next centre, by the full common-centre
square and the explicit UV=0 origin. Therefore the entire tail is unchanged
there. This retains all earlier outer exceptional/branch portions as schemes,
with their exact global/node maps, rather than as selected points. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale


namespace Run.Step
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π} {m : ℕ}
  (S : State X q₀ π hπ (m + 3) (Nat.succ_pos (m + 2)))
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (tail : Run hex hp hatlas hbc (S.step hex hp hatlas hbc (Nat.succ_pos m)))

lemma positive_origin_not_mem_uv (z : Spec (.of (ResidueField R))) :
    NextCenter.origin π hπ (m + 1) (by omega) z ∉
      (Resolution.uOpen π (m + 1) ⊔ Resolution.vOpen π (m + 1)) := by
  intro hz
  rcases hz with hz | hz
  · change PlaneNode.U (π ^ (m + 1)) ∉
      (NextCenter.origin π hπ (m + 1) (by omega) z).asIdeal at hz
    apply hz
    change PlaneNode.residueMap (π ^ (m + 1))
      (IsDiscreteValuationRing.power_residue_zero π hπ (m + 1) (by omega))
      (PlaneNode.U (π ^ (m + 1))) ∈ z.asIdeal
    simp [PlaneNode.residueMap]
  · change PlaneNode.V (π ^ (m + 1)) ∉
      (NextCenter.origin π hπ (m + 1) (by omega) z).asIdeal at hz
    apply hz
    change PlaneNode.residueMap (π ^ (m + 1))
      (IsDiscreteValuationRing.power_residue_zero π hπ (m + 1) (by omega))
      (PlaneNode.V (π ^ (m + 1))) ∈ z.asIdeal
    simp [PlaneNode.residueMap]

/-- The entire actual common outer open, mapped to the same global blowup. -/
def currentOuterToGlobal : (currentOuterOpen S hex hp hatlas).toScheme ⟶ (S.blowup hex).Y :=
  (currentOuterOpen S hex hp hatlas).ι ≫
    Chart.Step.toGlobal S.chart (S.blowup hex) (S.commonBlowup hex)

lemma currentOuter_disjoint :
    Disjoint (Set.range (currentOuterToGlobal S hex hp hatlas))
      (Set.range (S.step hex hp hatlas hbc (Nat.succ_pos m)).chart.globalPoint) := by
  let := S.blowup_proper hex hp
  let D := OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas
  have hr := Scheme.Pullback.Transport.range_eq_preimage_of_isPullback
    (Chart.Step.commonPoint_global_square S.chart D (S.blowup hex) (S.commonBlowup hex)
      (Nat.succ_pos m) hbc)
  apply Set.disjoint_left.mpr
  rintro z ⟨a, rfl⟩ hz
  have ha : (currentOuterOpen S hex hp hatlas).ι a ∈
      Set.range (Chart.Step.commonPoint S.chart D (S.commonBlowup hex) (by omega) hbc) := by
    rw [hr]
    exact hz
  obtain ⟨r, heq⟩ := ha
  have ho : Chart.Step.toNode S.chart D (S.commonBlowup hex)
      (Chart.Step.commonPoint S.chart D (S.commonBlowup hex) (by omega) hbc r) ∈
      Resolution.outerOpen D hπ := by
    rw [heq]
    exact a.property
  rw [← Scheme.Hom.comp_apply, Chart.Step.commonPoint_node] at ho
  have hv : NextCenter.origin π hπ (m + 1) (by omega) r ∈
      BlowupAtlas.middleChartMap D.atlas hπ ⁻¹ᵁ Resolution.outerOpen D hπ := ho
  rw [Resolution.middle_preimage_outer] at hv
  exact positive_origin_not_mem_uv (π := π) (hπ := hπ) r hv

lemma retainedOuter_square :
    IsPullback (retainedOuterInclusion S hex hp hatlas hbc tail ≫
      retainedToGlobal S hex hp hatlas hbc tail)
      (pullback.snd (retainedToBlowup S hex hp hatlas hbc tail)
        (currentOuterOpen S hex hp hatlas).ι)
      tail.map (currentOuterToGlobal S hex hp hatlas) := by
  exact (IsPullback.of_hasPullback (retainedToBlowup S hex hp hatlas hbc tail)
    (currentOuterOpen S hex hp hatlas).ι).paste_horiz
      (retained_square S hex hp hatlas hbc tail)

/-- All tail blowups leave this whole outer scheme unchanged. -/
lemma retainedOuter_projection_isIso : IsIso
    (pullback.snd (retainedToBlowup S hex hp hatlas hbc tail)
      (currentOuterOpen S hex hp hatlas).ι) := by
  let := Run.retained_projection_isIso tail (currentOuterToGlobal S hex hp hatlas)
    (currentOuter_disjoint S hex hp hatlas hbc)
  rw [← (retainedOuter_square S hex hp hatlas hbc tail).isoPullback_hom_snd]
  infer_instance

/-- Identify the retained outer piece with the current outer open, unchanged by the tail run. -/
def retainedOuterIso : retainedOuter S hex hp hatlas hbc tail ≅
    (currentOuterOpen S hex hp hatlas).toScheme := by
  letI := retainedOuter_projection_isIso S hex hp hatlas hbc tail
  exact asIso (pullback.snd (retainedToBlowup S hex hp hatlas hbc tail)
    (currentOuterOpen S hex hp hatlas).ι)

@[reassoc] lemma retainedOuterIso_triangle :
    (retainedOuterIso S hex hp hatlas hbc tail).hom ≫
      (currentOuterOpen S hex hp hatlas).ι =
      retainedOuterInclusion S hex hp hatlas hbc tail ≫
        retainedToBlowup S hex hp hatlas hbc tail := pullback.condition.symm

/-- The retained chart's global map is the unique unchanged lift of precisely
the original outer map. -/
@[reassoc] lemma retainedOuter_global_map :
    (retainedOuterIso S hex hp hatlas hbc tail).hom ≫
      Run.retainedMap tail (currentOuterToGlobal S hex hp hatlas)
        (currentOuter_disjoint S hex hp hatlas hbc) =
      retainedOuterInclusion S hex hp hatlas hbc tail ≫
        retainedToGlobal S hex hp hatlas hbc tail := by
  apply Run.retainedMap_unique
  exact (retainedOuter_square S hex hp hatlas hbc tail).w

end Run.Step
end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end PointedRunOuterRetention


section PointedRunMiddleSquares

/-! The successor's actual common chart remains the full cartesian middle chart
of the preceding common blowup. This is the square needed to paste the genuine
inductive node comparison, after the proved top-shrink identification. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run.Step
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π} {m : ℕ}
  (S : State X q₀ π hπ (m + 3) (Nat.succ_pos (m + 2)))
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})

lemma currentMiddle_node_square :
    IsPullback (currentMiddleMap S hex hp hatlas hbc)
      (S.step hex hp hatlas hbc (Nat.succ_pos m)).chart.toNode
      (Chart.Step.toNode S.chart (OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas)
        (S.commonBlowup hex))
      (BlowupAtlas.middleChartMap
        (OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas).atlas hπ) := by
  let := S.blowup_proper hex hp
  let := nextToMiddle_isIso S hex hp hatlas hbc
  refine IsPullback.of_iso_pullback ⟨?_⟩
    (asIso (currentMiddleToRaw S hex hp hatlas hbc)) ?_ ?_
  · simp only [currentMiddleMap, currentMiddleToRaw, Category.assoc,
      Chart.Step.middle_square]
    rfl
  · rfl
  · exact Chart.Step.nextToMiddle_node _ _ _ _ _ _

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run.Step

end -- noncomputable section
end PointedRunMiddleSquares


section PointedRunComparisonCharts

/-! Exact charts for the inductive full comparison. The only local comparison
premise is the actual cartesian square already produced for the literal tail;
all outer maps, middle maps, and contraction rectangles are then constructed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run.Step.Comparison
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π} {m : ℕ}
  (S : State X q₀ π hπ (m + 3) (Nat.succ_pos (m + 2)))
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (tail : Run hex hp hatlas hbc (S.step hex hp hatlas hbc (Nat.succ_pos m)))
  (E : Resolution.Data π (m + 1))
  (F : tail.fullCommon ⟶ E.Y)
  (HF : IsPullback F tail.fullCommonMap E.map
    (S.step hex hp hatlas hbc (Nat.succ_pos m)).chart.toNode)

local notation "D" => OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas

/-- Map the retained middle piece to the exponent-reduced resolution source using `F`. -/
def middleNodeMap : retainedMiddle S hex hp hatlas hbc tail ⟶ E.Y :=
  (retainedMiddleIso S hex hp hatlas hbc tail).hom ≫ F

/-- Map the retained middle piece into the glued resolution source through its modified chart. -/
def middleLocalMap : retainedMiddle S hex hp hatlas hbc tail ⟶ (Resolution.step D hπ E).Y :=
  middleNodeMap S hex hp hatlas hbc tail E F ≫ Resolution.stepModifiedChart D hπ E

/-- Map the retained outer piece to the outer open of the node blowup. -/
def outerNodeMap : retainedOuter S hex hp hatlas hbc tail ⟶ (Resolution.outerOpen D hπ).toScheme :=
  (retainedOuterIso S hex hp hatlas hbc tail).hom ≫
    (Chart.Step.toNode S.chart D (S.commonBlowup hex) ∣_ Resolution.outerOpen D hπ)

/-- Map the retained outer piece into the glued resolution source through its unchanged chart. -/
def outerLocalMap : retainedOuter S hex hp hatlas hbc tail ⟶ (Resolution.step D hπ E).Y :=
  outerNodeMap S hex hp hatlas hbc tail ≫ Resolution.stepUnchangedChart D hπ E

include HF in
lemma middleNode_square :
    IsPullback (middleNodeMap S hex hp hatlas hbc tail E F)
      (pullback.snd (retainedToBlowup S hex hp hatlas hbc tail) (currentMiddleMap S hex hp hatlas
        hbc))
      E.map (S.step hex hp hatlas hbc (Nat.succ_pos m)).chart.toNode := by
  apply HF.of_iso (retainedMiddleIso S hex hp hatlas hbc tail).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [middleNodeMap]
  · change tail.fullCommonMap = (retainedMiddleIso S hex hp hatlas hbc tail).inv ≫ _
    calc
      tail.fullCommonMap = (retainedMiddleIso S hex hp hatlas hbc tail).inv ≫
          ((retainedMiddleIso S hex hp hatlas hbc tail).hom ≫ tail.fullCommonMap) := by
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = _ := by rw [retainedMiddleIso_hom_chart]
  · simp
  · simp

include HF in
/-- The retained recursive chart is cartesian over the preceding common/node
blowup, with the literal middle-to-blowup map. -/
lemma middle_rectangle :
    IsPullback (middleNodeMap S hex hp hatlas hbc tail E F)
      (retainedMiddleInclusion S hex hp hatlas hbc tail ≫ retainedToBlowup S hex hp hatlas hbc tail)
      (E.map ≫ BlowupAtlas.middleChartMap (D).atlas hπ)
      (Chart.Step.toNode S.chart D (S.commonBlowup hex)) := by
  have H := (middleNode_square S hex hp hatlas hbc tail E F HF).paste_vert
    (currentMiddle_node_square S hex hp hatlas hbc).flip
  simpa only [retainedMiddleInclusion, pullback.condition] using H

lemma outer_rectangle :
    IsPullback (outerNodeMap S hex hp hatlas hbc tail)
      (retainedOuterInclusion S hex hp hatlas hbc tail ≫ retainedToBlowup S hex hp hatlas hbc tail)
      (Resolution.outerOpen D hπ).ι
      (Chart.Step.toNode S.chart D (S.commonBlowup hex)) := by
  apply (isPullback_morphismRestrict (Chart.Step.toNode S.chart D (S.commonBlowup hex))
    (Resolution.outerOpen D hπ)).of_iso
    (retainedOuterIso S hex hp hatlas hbc tail).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [outerNodeMap]
  · rw [← retainedOuterIso_triangle S hex hp hatlas hbc tail]
    simp
    rfl
  · simp
  · simp

include HF in
@[reassoc] lemma middle_contraction :
    middleLocalMap S hex hp hatlas hbc tail E F ≫ Resolution.stepToBlowup D hπ E =
      retainedMiddleInclusion S hex hp hatlas hbc tail ≫
        retainedToBlowup S hex hp hatlas hbc tail ≫
          Chart.Step.toNode S.chart D (S.commonBlowup hex) := by
  rw [middleLocalMap, Category.assoc, ← (Resolution.stepModifiedChart_isPullback D hπ E).w]
  simpa only [Category.assoc] using (middle_rectangle S hex hp hatlas hbc tail E F HF).w

@[reassoc] lemma outer_contraction :
    outerLocalMap S hex hp hatlas hbc tail E ≫ Resolution.stepToBlowup D hπ E =
      retainedOuterInclusion S hex hp hatlas hbc tail ≫
        retainedToBlowup S hex hp hatlas hbc tail ≫
          Chart.Step.toNode S.chart D (S.commonBlowup hex) := by
  rw [outerLocalMap, Category.assoc, ← (Resolution.stepUnchangedChart_isPullback D hπ E).w,
    Category.id_comp]
  simpa only [Category.assoc] using (outer_rectangle S hex hp hatlas hbc tail).w

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run.Step.Comparison

end -- noncomputable section
end PointedRunComparisonCharts




section PointedRunComparisonGluing

/-! Glue the genuine full-source inductive comparison on its retained middle
and unchanged outer pieces. The overlap is checked scheme-theoretically using
the unchanged chart's identity pullback square. Both source-chart squares and
all local rectangles are proved before cartesian locality is applied. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run.Step.Comparison
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π} {m : ℕ}
  (S : State X q₀ π hπ (m + 3) (Nat.succ_pos (m + 2)))
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (tail : Run hex hp hatlas hbc (S.step hex hp hatlas hbc (Nat.succ_pos m)))
  (E : Resolution.Data π (m + 1)) (F : tail.fullCommon ⟶ E.Y)
  (HF : IsPullback F tail.fullCommonMap E.map
    (S.step hex hp hatlas hbc (Nat.succ_pos m)).chart.toNode)

local notation "D" => OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas
local notation "iM" => retainedMiddleInclusion S hex hp hatlas hbc tail
local notation "iO" => retainedOuterInclusion S hex hp hatlas hbc tail
local notation "aM" => middleNodeMap S hex hp hatlas hbc tail E F
local notation "aO" => outerNodeMap S hex hp hatlas hbc tail
local notation "fM" => middleLocalMap S hex hp hatlas hbc tail E F
local notation "fO" => outerLocalMap S hex hp hatlas hbc tail E
local notation "jM" => Resolution.stepModifiedChart D hπ E
local notation "jO" => Resolution.stepUnchangedChart D hπ E
local notation "v" => Resolution.stepToBlowup D hπ E
local notation "b" => retainedToBlowup S hex hp hatlas hbc tail
local notation "t" => Chart.Step.toNode S.chart D (S.commonBlowup hex)

include HF in
lemma local_overlap : pullback.fst iM iO ≫ fM = pullback.snd iM iO ≫ fO := by
  have H : (pullback.fst iM iO ≫ fM) ≫ v =
      (pullback.snd iM iO ≫ aO) ≫ (Resolution.outerOpen D hπ).ι := by
    calc
      (pullback.fst iM iO ≫ fM) ≫ v = pullback.fst iM iO ≫ iM ≫ b ≫ t := by
        rw [Category.assoc, middle_contraction S hex hp hatlas hbc tail E F HF]
      _ = pullback.snd iM iO ≫ iO ≫ b ≫ t := by
        rw [← Category.assoc, pullback.condition, Category.assoc]
      _ = (pullback.snd iM iO ≫ aO) ≫ (Resolution.outerOpen D hπ).ι := by
        simpa only [Category.assoc] using congrArg (fun f => pullback.snd iM iO ≫ f)
          (outer_rectangle S hex hp hatlas hbc tail).w.symm
  simpa only [outerLocalMap, Category.assoc] using
    Scheme.SourceOpenCover.eq_comp_of_identity_square jO v (Resolution.outerOpen D hπ).ι
      (Resolution.stepUnchangedChart_isPullback D hπ E).flip
      (pullback.fst iM iO ≫ fM) (pullback.snd iM iO ≫ aO) H

/-- A genuine map on the entire retained source, obtained by source-open gluing. -/
def gluedComparison : retainedCommon S hex hp hatlas hbc tail ⟶ (Resolution.step D hπ E).Y :=
  Scheme.SourceOpenCover.glueTwo iM iO (retained_charts_cover S hex hp hatlas hbc tail) fM fO
    (local_overlap S hex hp hatlas hbc tail E F HF)

local notation "φ" => gluedComparison S hex hp hatlas hbc tail E F HF

@[reassoc (attr := simp)] lemma middle_gluedComparison : iM ≫ φ = fM :=
  Scheme.SourceOpenCover.left_glueTwo _ _ _ _ _ _

@[reassoc (attr := simp)] lemma outer_gluedComparison : iO ≫ φ = fO :=
  Scheme.SourceOpenCover.right_glueTwo _ _ _ _ _ _

@[reassoc] lemma gluedComparison_triangle : φ ≫ v = b ≫ t := by
  exact Scheme.SourceOpenCover.glueTwo_comp _ _ _ _ _ _ v (b ≫ t)
    (middle_contraction S hex hp hatlas hbc tail E F HF)
    (outer_contraction S hex hp hatlas hbc tail E)

lemma middle_gluedComparison_range : φ ⁻¹ᵁ (jM).opensRange = (iM).opensRange := by
  apply TopologicalSpace.Opens.ext
  change φ ⁻¹' Set.range jM = Set.range (pullback.fst b (currentMiddleMap S hex hp hatlas hbc))
  rw [Scheme.Pullback.Transport.range_eq_preimage_of_isPullback
      (Resolution.stepModifiedChart_isPullback D hπ E).flip,
    Scheme.Pullback.range_fst, currentMiddleMap_range]
  ext z
  change v (φ z) ∈ Set.range (BlowupAtlas.middleChartMap (D).atlas hπ) ↔
    t (b z) ∈ Set.range (BlowupAtlas.middleChartMap (D).atlas hπ)
  rw [← Scheme.Hom.comp_apply, gluedComparison_triangle]
  rfl

lemma outer_gluedComparison_range : φ ⁻¹ᵁ (jO).opensRange = (iO).opensRange := by
  apply TopologicalSpace.Opens.ext
  change φ ⁻¹' Set.range jO = Set.range (pullback.fst b (currentOuterOpen S hex hp hatlas).ι)
  rw [Scheme.Pullback.Transport.range_eq_preimage_of_isPullback
      (Resolution.stepUnchangedChart_isPullback D hπ E).flip,
    Scheme.Pullback.range_fst]
  simp only [Scheme.Opens.range_ι]
  ext z
  change v (φ z) ∈ Resolution.outerOpen D hπ ↔ t (b z) ∈ Resolution.outerOpen D hπ
  rw [← Scheme.Hom.comp_apply, gluedComparison_triangle]
  rfl

/-- Full cartesian compatibility follows from the proved source chart squares
and the actual middle/outer rectangles, never merely from point coverage. -/
lemma gluedComparison_square : IsPullback φ b v t := by
  have cover : ∀ z : (Resolution.step D hπ E).Y,
      z ∈ Set.range jM ∨ z ∈ Set.range jO := by
    intro z
    exact AlgebraicGeometry.Scheme.OpenPushout.Modification.OfRestriction.charts_cover E.map
      (BlowupAtlas.middleChartMap (D).atlas hπ) (Resolution.outerOpen D hπ) z
  let U := Scheme.SourceOpenCover.twoOpenCover jM jO cover
  let Wi : Bool → Scheme.{u}
    | false => retainedMiddle S hex hp hatlas hbc tail
    | true => retainedOuter S hex hp hatlas hbc tail
  let si : ∀ k : Bool, Wi k ⟶ retainedCommon S hex hp hatlas hbc tail
    | false => iM
    | true => iO
  let li : ∀ k : Bool, Wi k ⟶ U.X k
    | false => aM
    | true => aO
  let (k : Bool) : IsOpenImmersion (si k) := by
    cases k <;> dsimp [si] <;> infer_instance
  apply Scheme.SourceOpenCover.isPullback_of_openCover_ranges φ b v t U Wi si li
  · intro k
    cases k
    · change iM ≫ φ = aM ≫ jM
      exact middle_gluedComparison S hex hp hatlas hbc tail E F HF
    · change iO ≫ φ = aO ≫ jO
      exact outer_gluedComparison S hex hp hatlas hbc tail E F HF
  · intro k
    cases k
    · exact middle_gluedComparison_range S hex hp hatlas hbc tail E F HF
    · exact outer_gluedComparison_range S hex hp hatlas hbc tail E F HF
  · intro k
    cases k
    · change IsPullback aM (iM ≫ b) (jM ≫ v) t
      rw [← (Resolution.stepModifiedChart_isPullback D hπ E).w]
      exact middle_rectangle S hex hp hatlas hbc tail E F HF
    · change IsPullback aO (iO ≫ b) (jO ≫ v) t
      rw [← (Resolution.stepUnchangedChart_isPullback D hπ E).w, Category.id_comp]
      exact outer_rectangle S hex hp hatlas hbc tail

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run.Step.Comparison

end -- noncomputable section
end PointedRunComparisonGluing
