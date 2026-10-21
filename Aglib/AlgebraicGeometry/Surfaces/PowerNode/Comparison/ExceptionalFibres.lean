/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.RecursiveComponents
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.PointedRunTransport

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.ExceptionalFibres`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`49b93a9c888e6ad7e81182262630f2da5ecbc33f2537c866c2d84ce01b0b7269`.
Actual node/pointed scheme maps, full covers, original structural triangles and source quantifiers
  are retained. Universal blowup inputs remain conditional.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre

/-!
# Node comparison, literal exceptional fibres, and chain coverage

This module preserves the conditional interfaces and source-coverage boundaries
recorded in the individual sections below.
-/

section NodeResolutionIdentityReplacement

/-! Replacing the middle chart by an isomorphic source leaves the ENTIRE
one-step blowup unchanged as a scheme. This proves the full exponent-two base
case for comparing the actual global Run with the independently glued node
resolution; it is stronger than identifying only its exceptional points. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {π : R} {m : ℕ} (B : OneStepBlowup.Data π m) (hπ : Irreducible π)
  (E : Data π m)

lemma stepToBlowup_isIso [IsIso E.map] : IsIso (stepToBlowup B hπ E) := by
  let U : B.blowup.Y.OpenCover := {
    I₀ := Bool
    X := fun | false => Resolution.X π m | true => (outerOpen B hπ).toScheme
    f := fun | false => BlowupAtlas.middleChartMap B.atlas hπ | true => (outerOpen B hπ).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      constructor
      · intro z
        have hz : z ∈ (BlowupAtlas.middleChartMap B.atlas hπ).opensRange ⊔ outerOpen B hπ := by
          rw [middle_outer_cover]
          trivial
        rcases hz with ⟨y, hy⟩ | hz
        · exact ⟨false, y, hy⟩
        · exact ⟨true, ⟨z, hz⟩, rfl⟩
      · intro k
        cases k <;> infer_instance }
  apply IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme) U
  intro k
  cases k
  · change IsIso (pullback.snd (stepToBlowup B hπ E) (BlowupAtlas.middleChartMap B.atlas hπ))
    rw [← (stepModifiedChart_isPullback B hπ E).flip.isoPullback_inv_snd]
    infer_instance
  · change IsIso (pullback.snd (stepToBlowup B hπ E) (outerOpen B hπ).ι)
    rw [← (stepUnchangedChart_isPullback B hπ E).flip.isoPullback_inv_snd]
    infer_instance

variable (π : R) (hπ : Irreducible π)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u})

/-- Identifies the exponent-two resolution source with the source of its single blowup. -/
def resolveTwoBlowupIso : (resolve π hπ hex hp hatlas 2).Y ≅
    (OneStepBlowup.ofFamilies π 0 hex hp hatlas).blowup.Y := by
  let B := OneStepBlowup.ofFamilies π 0 hex hp hatlas
  letI : IsIso (zero π).map := by change IsIso (𝟙 _); infer_instance
  letI := stepToBlowup_isIso B hπ (zero π)
  exact asIso (stepToBlowup B hπ (zero π))

@[reassoc] lemma resolveTwoBlowupIso_triangle :
    (resolveTwoBlowupIso π hπ hex hp hatlas).hom ≫
      (OneStepBlowup.ofFamilies π 0 hex hp hatlas).blowup.map =
      (resolve π hπ hex hp hatlas 2).map := rfl

@[reassoc] lemma resolveTwoBlowupIso_inv_triangle :
    (resolveTwoBlowupIso π hπ hex hp hatlas).inv ≫
      (resolve π hπ hex hp hatlas 2).map =
      (OneStepBlowup.ofFamilies π 0 hex hp hatlas).blowup.map := by
  rw [← resolveTwoBlowupIso_triangle π hπ hex hp hatlas, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeResolutionIdentityReplacement


section PointedRunBaseComparisons

/-! The zero-blowup and one-blowup full source comparisons for the actual Run.
Both are proved cartesian against the literal independently constructed local
node resolution, with unchanged global/common/residue structural maps. -/
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
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})

variable (S : State X q₀ π hπ 1 Nat.zero_lt_one)

/-- The comparison from the full common chart of a one-step terminal run to the exponent-one node
source. -/
def oneNodeComparison : (Run.one S : Run hex hp hatlas hbc S).fullCommon ⟶
    (Resolution.resolve π hπ hex hp hatlas 1).Y :=
  (Run.one S).fullCommonMap ≫ S.chart.toNode

lemma oneNodeComparison_square :
    IsPullback (oneNodeComparison hex hp hatlas hbc S)
      (Run.one S : Run hex hp hatlas hbc S).fullCommonMap
      (Resolution.resolve π hπ hex hp hatlas 1).map S.chart.toNode := by
  let : IsIso (Run.one S : Run hex hp hatlas hbc S).fullCommonMap := by
    change IsIso (pullback.snd (𝟙 S.Y) S.chart.toGlobal)
    infer_instance
  let : IsIso (Resolution.resolve π hπ hex hp hatlas 1).map := by
    change IsIso (𝟙 _)
    infer_instance
  apply IsPullback.of_vert_isIso
  constructor
  simp only [oneNodeComparison, Resolution.resolve, Resolution.one, Category.comp_id]

variable (S : State X q₀ π hπ 2 (Nat.succ_pos 1))

/-- Identifies the common blowup source with the full common chart of the exponent-two run. -/
def twoFullCommonIso : (S.commonBlowup hex).Y ≅
    (Run.two S : Run hex hp hatlas hbc S).fullCommon :=
  (Chart.Step.global_square S.chart (S.blowup hex) (S.commonBlowup hex) hbc).isoPullback

@[reassoc (attr := simp)] lemma twoFullCommonIso_hom_global :
    (twoFullCommonIso hex hp hatlas hbc S).hom ≫ (Run.two S).fullCommonToGlobal =
      Chart.Step.toGlobal S.chart (S.blowup hex) (S.commonBlowup hex) :=
  (Chart.Step.global_square S.chart (S.blowup hex) (S.commonBlowup hex) hbc).isoPullback_hom_fst

@[reassoc (attr := simp)] lemma twoFullCommonIso_hom_chart :
    (twoFullCommonIso hex hp hatlas hbc S).hom ≫ (Run.two S).fullCommonMap =
      (S.commonBlowup hex).map :=
  (Chart.Step.global_square S.chart (S.blowup hex) (S.commonBlowup hex) hbc).isoPullback_hom_snd

/-- The comparison from the full common chart of the exponent-two run to its literal node
resolution. -/
def twoNodeComparison : (Run.two S : Run hex hp hatlas hbc S).fullCommon ⟶
    (Resolution.resolve π hπ hex hp hatlas 2).Y :=
  (twoFullCommonIso hex hp hatlas hbc S).inv ≫
    Chart.Step.toNode S.chart (OneStepBlowup.ofFamilies π 0 hex hp hatlas)
      (S.commonBlowup hex) ≫ (Resolution.resolveTwoBlowupIso π hπ hex hp hatlas).inv

lemma twoNodeComparison_square :
    IsPullback (twoNodeComparison hex hp hatlas hbc S)
      (Run.two S : Run hex hp hatlas hbc S).fullCommonMap
      (Resolution.resolve π hπ hex hp hatlas 2).map S.chart.toNode := by
  apply (Chart.Step.node_square S.chart (OneStepBlowup.ofFamilies π 0 hex hp hatlas)
    (S.commonBlowup hex) hbc).of_iso
    (twoFullCommonIso hex hp hatlas hbc S)
    (Resolution.resolveTwoBlowupIso π hπ hex hp hatlas).symm (Iso.refl _) (Iso.refl _)
  · simp [twoNodeComparison]
  · simp
  · simp [Resolution.resolveTwoBlowupIso_inv_triangle]
  · simp

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run

end -- noncomputable section
end PointedRunBaseComparisons


section PointedRunNodeComparison

/-! A constructive full-source comparison for EVERY actual finite Run. The
induction retains the entire outer piece, uses the genuine smaller-tail square
on the full middle, glues on the exact source-open cover, and proves the whole
cartesian square. The smaller-tail premise is discharged here by recursion. -/
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

/-- The comparison to the next literal resolution step obtained from the retained common chart and
the glued comparison. -/
def nextNodeComparison : (Run.next m S tail).fullCommon ⟶ (Resolution.step D hπ E).Y :=
  (retainedFullCommonIso S hex hp hatlas hbc tail).inv ≫
    gluedComparison S hex hp hatlas hbc tail E F HF

lemma nextNodeComparison_square :
    IsPullback (nextNodeComparison S hex hp hatlas hbc tail E F HF)
      (Run.next m S tail).fullCommonMap (Resolution.step D hπ E).map S.chart.toNode := by
  have H := (gluedComparison_square S hex hp hatlas hbc tail E F HF).paste_vert
    (Chart.Step.node_square S.chart D (S.commonBlowup hex) hbc)
  have H' : IsPullback (gluedComparison S hex hp hatlas hbc tail E F HF)
      (retainedToBlowup S hex hp hatlas hbc tail ≫ (S.commonBlowup hex).map)
      (Resolution.step D hπ E).map S.chart.toNode := H
  apply H'.of_iso (retainedFullCommonIso S hex hp hatlas hbc tail)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [nextNodeComparison]
  · simp
  · simp
  · simp

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run.Step.Comparison

namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π}
  {hex : NoetherianBlowupExistence.{u}} {hp : NoetherianBlowupProper.{u}}
  {hatlas : BlowupAffineAtlas.{u}} {hbc : BlowupFlatBaseChange.{u}}

/-- Actual output of induction on the given Run, not a supplied comparison
family or an assumption about its components. -/
def fullNodeComparisonData : {n : ℕ} → {hn : 0 < n} →
    {S : State X q₀ π hπ n hn} → (T : Run hex hp hatlas hbc S) →
    {f : T.fullCommon ⟶ (Resolution.resolve π hπ hex hp hatlas n).Y //
      IsPullback f T.fullCommonMap (Resolution.resolve π hπ hex hp hatlas n).map S.chart.toNode}
  | _, _, _, .one S =>
      ⟨oneNodeComparison hex hp hatlas hbc S, oneNodeComparison_square hex hp hatlas hbc S⟩
  | _, _, _, .two S =>
      ⟨twoNodeComparison hex hp hatlas hbc S, twoNodeComparison_square hex hp hatlas hbc S⟩
  | _, _, _, .next m S tail =>
      let previous := fullNodeComparisonData tail
      ⟨Step.Comparison.nextNodeComparison S hex hp hatlas hbc tail
          (Resolution.resolve π hπ hex hp hatlas (m + 1)) previous.val previous.property,
        Step.Comparison.nextNodeComparison_square S hex hp hatlas hbc tail
          (Resolution.resolve π hπ hex hp hatlas (m + 1)) previous.val previous.property⟩

variable {n : ℕ} {hn : 0 < n} {S : State X q₀ π hπ n hn}
  (T : Run hex hp hatlas hbc S)

/-- The recursively constructed comparison from a run's full common chart to the literal node
resolution. -/
def fullNodeComparison : T.fullCommon ⟶ (Resolution.resolve π hπ hex hp hatlas n).Y :=
  (fullNodeComparisonData T).val

lemma fullNodeComparison_square :
    IsPullback (fullNodeComparison T) T.fullCommonMap
      (Resolution.resolve π hπ hex hp hatlas n).map S.chart.toNode :=
  (fullNodeComparisonData T).property

@[reassoc (attr := simp)] lemma fullNodeComparison_triangle :
    fullNodeComparison T ≫ (Resolution.resolve π hπ hex hp hatlas n).map =
      T.fullCommonMap ≫ S.chart.toNode := (fullNodeComparison_square T).w

/-- The entire independently glued local resolution pulls back to exactly the
same entire common source as the actual global Run. Both projections are fixed. -/
def fullNodeComparisonIso : T.fullCommon ≅
    pullback (Resolution.resolve π hπ hex hp hatlas n).map S.chart.toNode :=
  (fullNodeComparison_square T).isoPullback

@[reassoc (attr := simp)] lemma fullNodeComparisonIso_hom_fst :
    (fullNodeComparisonIso T).hom ≫
      pullback.fst (Resolution.resolve π hπ hex hp hatlas n).map S.chart.toNode =
      fullNodeComparison T := (fullNodeComparison_square T).isoPullback_hom_fst

@[reassoc (attr := simp)] lemma fullNodeComparisonIso_hom_snd :
    (fullNodeComparisonIso T).hom ≫
      pullback.snd (Resolution.resolve π hπ hex hp hatlas n).map S.chart.toNode =
      T.fullCommonMap := (fullNodeComparison_square T).isoPullback_hom_snd

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run

end -- noncomputable section
end PointedRunNodeComparison


section PointedRunExceptionalComparison

/-! The full origin fibres of the independently glued local resolution and the
actual arbitrary finite global Run are isomorphic over the same literal residue
field. This follows from the full recursive source comparison, not from a
terminal-chart cover or repeated first-step exceptional identifications. -/
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
local notation "E" => Resolution.resolve π hπ hex hp hatlas n
local notation "origin" => NextCenter.origin π hπ n hn

lemma fullCommon_node_exceptional_square :
    IsPullback (pullback.fst T.fullCommonMap S.chart.point ≫ T.fullNodeComparison)
      (pullback.snd T.fullCommonMap S.chart.point) (E).map origin := by
  simpa only [S.chart.point_node] using
    (IsPullback.of_hasPullback T.fullCommonMap S.chart.point).paste_horiz
      T.fullNodeComparison_square

/-- Identifies the exceptional fibre in the full common chart with the exceptional fibre of the
literal node resolution. -/
def commonNodeExceptionalIso : pullback T.fullCommonMap S.chart.point ≅ pullback (E).map origin :=
  (fullCommon_node_exceptional_square T).isoPullback

@[reassoc (attr := simp)] lemma commonNodeExceptionalIso_hom_fst :
    (commonNodeExceptionalIso T).hom ≫ pullback.fst (E).map origin =
      pullback.fst T.fullCommonMap S.chart.point ≫ T.fullNodeComparison :=
  (fullCommon_node_exceptional_square T).isoPullback_hom_fst

@[reassoc (attr := simp)] lemma commonNodeExceptionalIso_hom_snd :
    (commonNodeExceptionalIso T).hom ≫ pullback.snd (E).map origin =
      pullback.snd T.fullCommonMap S.chart.point :=
  (fullCommon_node_exceptional_square T).isoPullback_hom_snd

/-- The desired whole exceptional-scheme comparison for the same given Run. -/
def exceptionalComparisonIso : pullback (E).map origin ≅ pullback T.map S.chart.globalPoint :=
  (commonNodeExceptionalIso T).symm ≪≫ T.fullCommonExceptionalIso

@[reassoc (attr := simp)] lemma exceptionalComparisonIso_hom_snd :
    (exceptionalComparisonIso T).hom ≫ pullback.snd T.map S.chart.globalPoint =
      pullback.snd (E).map origin := by
  simp only [exceptionalComparisonIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    fullCommonExceptionalIso_hom_snd]
  rw [← commonNodeExceptionalIso_hom_snd T, Iso.inv_hom_id_assoc]

/-- The morphism from the literal node exceptional fibre to the global source of the run. -/
def exceptionalToGlobal : pullback (E).map origin ⟶ T.source :=
  (exceptionalComparisonIso T).hom ≫ pullback.fst T.map S.chart.globalPoint

lemma exceptionalToGlobal_square :
    IsPullback (exceptionalToGlobal T) (pullback.snd (E).map origin) T.map S.chart.globalPoint := by
  apply IsPullback.of_iso_pullback _ (exceptionalComparisonIso T) rfl
    (exceptionalComparisonIso_hom_snd T)
  constructor
  simp only [Category.assoc, pullback.condition,
    exceptionalComparisonIso_hom_snd_assoc]

/-- Maximal irreducible components correspond because the actual schemes are
isomorphic. No cardinality or component family is provided as a premise. -/
def exceptionalIrreducibleComponentsEquiv :
    irreducibleComponents ↥(pullback (E).map origin) ≃
      irreducibleComponents ↥(pullback T.map S.chart.globalPoint) :=
  (irreducibleComponentsEquivOfIsPreirreducibleFiber
    (exceptionalComparisonIso T).hom (exceptionalComparisonIso T).hom.continuous
    (exceptionalComparisonIso T).hom.homeomorph.isOpenMap
    (fun _ => (Set.subsingleton_singleton.preimage
      (exceptionalComparisonIso T).hom.homeomorph.injective).isPreirreducible)
    (exceptionalComparisonIso T).hom.homeomorph.surjective).toEquiv.symm

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run

end -- noncomputable section
end PointedRunExceptionalComparison


section NodeLiteralExceptionalFibre

/-! The literal exceptional fibre, its closed inclusion in the same resolved
special fibre, and actual projective-line factor maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) (hπ : Irreducible π)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (ha : BlowupAffineAtlas.{u})
local notation "k" => IsLocalRing.ResidueField R

instance literalResidueBase_closed : IsClosedImmersion (residueBase (R := R)) :=
  IsClosedImmersion.spec_of_surjective _ (IsLocalRing.residue_surjective (R := R))

lemma originalNode_eq_origin (q : ℕ) : originalNode hπ q =
    NextCenter.origin π hπ (q + 1) (Nat.succ_pos _) := by
  rfl

/-- This is the actual pullback of the full resolution map at the original node. -/
abbrev literalExceptionalFibre (q : ℕ) : Scheme.{u} :=
  pullback (resolve π hπ hex hp ha (q + 1)).map (originalNode hπ q)

/-- The morphism from the literal exceptional fibre into the resolved special fibre, using the
original node's residue-field base. -/
def exceptionalToSpecial (q : ℕ) : literalExceptionalFibre π hπ hex hp ha q ⟶
    sourceSpecialFibre (resolve π hπ hex hp ha (q + 1)) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
    rw [← Category.assoc, pullback.condition, Category.assoc, originalNode_base])

@[reassoc (attr := simp)] lemma exceptionalToSpecial_fst (q : ℕ) :
    exceptionalToSpecial π hπ hex hp ha q ≫
      pullback.fst ((resolve π hπ hex hp ha (q + 1)).map ≫ base) residueBase =
        pullback.fst (resolve π hπ hex hp ha (q + 1)).map (originalNode hπ q) :=
  pullback.lift_fst ..
@[reassoc (attr := simp)] lemma exceptionalToSpecial_snd (q : ℕ) :
    exceptionalToSpecial π hπ hex hp ha q ≫
      pullback.snd ((resolve π hπ hex hp ha (q + 1)).map ≫ base) residueBase =
        pullback.snd (resolve π hπ hex hp ha (q + 1)).map (originalNode hπ q) :=
  pullback.lift_snd ..

instance exceptionalToSpecial_closed (q : ℕ) :
    IsClosedImmersion (exceptionalToSpecial π hπ hex hp ha q) := by
  let p := pullback.fst ((resolve π hπ hex hp ha (q + 1)).map ≫ base) residueBase
  have : IsClosedImmersion (exceptionalToSpecial π hπ hex hp ha q ≫ p) := by
    dsimp [p]
    rw [exceptionalToSpecial_fst]
    infer_instance
  exact IsClosedImmersion.of_comp _ p

/-- The full exceptional scheme, not a pointwise surrogate, is the residue-node
pullback inside the literal special fibre. -/
lemma exceptionalToSpecial_square (q : ℕ) :
    IsPullback (exceptionalToSpecial π hπ hex hp ha q)
      (pullback.snd (resolve π hπ hex hp ha (q + 1)).map (originalNode hπ q))
      (pullback.fst ((resolve π hπ hex hp ha (q + 1)).map ≫ base) residueBase ≫
        (resolve π hπ hex hp ha (q + 1)).map) (originalNode hπ q) := by
  let E := resolve π hπ hex hp ha (q + 1)
  let e := exceptionalToSpecial π hπ hex hp ha q
  have hw : e ≫ (pullback.fst (E.map ≫ base) residueBase ≫ E.map) =
      pullback.snd E.map (originalNode hπ q) ≫ originalNode hπ q := by
    rw [← Category.assoc, exceptionalToSpecial_fst, pullback.condition]
  apply IsPullback.of_isLimit (c := PullbackCone.mk e (pullback.snd _ _) hw)
  refine PullbackCone.IsLimit.mk _
    (fun s => pullback.lift (s.fst ≫ pullback.fst (E.map ≫ base) residueBase) s.snd
      (by simpa only [Category.assoc] using s.condition)) ?_ ?_ ?_
  · intro s
    apply (cancel_mono (pullback.fst (E.map ≫ base) residueBase)).mp
    simp only [Category.assoc, e, E, exceptionalToSpecial_fst, pullback.lift_fst]
  · intro s
    exact pullback.lift_snd ..
  · intro s m hm₁ hm₂
    apply pullback.hom_ext
    · rw [pullback.lift_fst, ← exceptionalToSpecial_fst π hπ hex hp ha q,
        ← Category.assoc]
      exact congrArg (· ≫ pullback.fst (E.map ≫ base) residueBase) hm₁
    · exact hm₂.trans (pullback.lift_snd ..).symm

/-- The accepted actual P1 morphism factors through the literal origin fibre. -/
def exceptionalP1 (q : ℕ) (i : Fin q) : projectiveP1 k ⟶
    literalExceptionalFibre π hπ hex hp ha q :=
  pullback.lift
    (interiorComponent π hπ hex hp ha q i ≫
      pullback.fst ((resolve π hπ hex hp ha (q + 1)).map ≫ base) residueBase)
    (structureMap k) (interiorComponent_target π hπ hex hp ha q i)

@[reassoc (attr := simp)] lemma exceptionalP1_special (q : ℕ) (i : Fin q) :
    exceptionalP1 π hπ hex hp ha q i ≫ exceptionalToSpecial π hπ hex hp ha q =
      interiorComponent π hπ hex hp ha q i := by
  apply (cancel_mono (pullback.fst ((resolve π hπ hex hp ha (q + 1)).map ≫ base) residueBase)).mp
  simp only [Category.assoc, exceptionalToSpecial_fst, exceptionalP1, pullback.lift_fst]

@[reassoc (attr := simp)] lemma exceptionalP1_base (q : ℕ) (i : Fin q) :
    exceptionalP1 π hπ hex hp ha q i ≫
      pullback.snd (resolve π hπ hex hp ha (q + 1)).map (originalNode hπ q) = structureMap k :=
  pullback.lift_snd ..

instance exceptionalP1_closed (q : ℕ) (i : Fin q) :
    IsClosedImmersion (exceptionalP1 π hπ hex hp ha q i) := by
  have : IsClosedImmersion (exceptionalP1 π hπ hex hp ha q i ≫
      exceptionalToSpecial π hπ hex hp ha q) := by
    rw [exceptionalP1_special]
    exact interiorComponent_closedImmersion π hπ hex hp ha q i
  exact IsClosedImmersion.of_comp _ (exceptionalToSpecial π hπ hex hp ha q)

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeLiteralExceptionalFibre


section NodeExceptionalEndFibres

/-! Exact scheme-theoretic pullbacks of both actual affine ends to the full
exceptional fibre. These reduced residue points are absorbed by the end P1s. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) (hπ : Irreducible π)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (ha : BlowupAffineAtlas.{u})
local notation "k" => IsLocalRing.ResidueField R

@[reassoc] lemma leftEndpoint_target (q : ℕ) :
    Cross.endpoint k ≫ resolveLeftEnd π hπ hex hp ha q ≫
      pullback.fst ((resolve π hπ hex hp ha (q + 1)).map ≫ base) residueBase ≫
      (resolve π hπ hex hp ha (q + 1)).map = originalNode hπ q := by
  rw [resolveLeftEnd_target, Cross.endpoint, originalNode, ← Spec.map_comp]
  congr 1
  have H : ((aeval (0 : k)).restrictScalars R).comp
      (residueLeftHom (π ^ (q + 1)) (residue_uniformizer_pow hπ q)) =
        residueOriginHom (π ^ (q + 1)) (residue_uniformizer_pow hπ q) := by
    apply PlaneNode.hom_ext <;> simp [residueLeftHom, residueOriginHom]
  exact congrArg (fun f => CommRingCat.ofHom f.toRingHom) H

@[reassoc] lemma rightEndpoint_target (q : ℕ) :
    Cross.endpoint k ≫ resolveRightEnd π hπ hex hp ha q ≫
      pullback.fst ((resolve π hπ hex hp ha (q + 1)).map ≫ base) residueBase ≫
      (resolve π hπ hex hp ha (q + 1)).map = originalNode hπ q := by
  rw [resolveRightEnd_target, Cross.endpoint, originalNode, ← Spec.map_comp]
  congr 1
  have H : ((aeval (0 : k)).restrictScalars R).comp
      (residueRightHom (π ^ (q + 1)) (residue_uniformizer_pow hπ q)) =
        residueOriginHom (π ^ (q + 1)) (residue_uniformizer_pow hπ q) := by
    apply PlaneNode.hom_ext <;> simp [residueRightHom, residueOriginHom]
  exact congrArg (fun f => CommRingCat.ofHom f.toRingHom) H

/-- The endpoint of the left affine end, lifted to the literal exceptional fibre. -/
def leftExceptionalPoint (q : ℕ) : Spec (.of k) ⟶ literalExceptionalFibre π hπ hex hp ha q :=
  pullback.lift (Cross.endpoint k ≫ resolveLeftEnd π hπ hex hp ha q ≫
      pullback.fst ((resolve π hπ hex hp ha (q + 1)).map ≫ base) residueBase)
    (𝟙 _) (by
      simpa only [Category.assoc, Category.id_comp] using
        (leftEndpoint_target π hπ hex hp ha q))

/-- The endpoint of the right affine end, lifted to the literal exceptional fibre. -/
def rightExceptionalPoint (q : ℕ) : Spec (.of k) ⟶ literalExceptionalFibre π hπ hex hp ha q :=
  pullback.lift (Cross.endpoint k ≫ resolveRightEnd π hπ hex hp ha q ≫
      pullback.fst ((resolve π hπ hex hp ha (q + 1)).map ≫ base) residueBase)
    (𝟙 _) (by
      simpa only [Category.assoc, Category.id_comp] using
        (rightEndpoint_target π hπ hex hp ha q))

@[reassoc (attr := simp)] lemma leftExceptionalPoint_special (q : ℕ) :
    leftExceptionalPoint π hπ hex hp ha q ≫ exceptionalToSpecial π hπ hex hp ha q =
      Cross.endpoint k ≫ resolveLeftEnd π hπ hex hp ha q := by
  apply (cancel_mono (pullback.fst ((resolve π hπ hex hp ha (q + 1)).map ≫ base) residueBase)).mp
  simp only [Category.assoc, exceptionalToSpecial_fst, leftExceptionalPoint, pullback.lift_fst]
@[reassoc (attr := simp)] lemma rightExceptionalPoint_special (q : ℕ) :
    rightExceptionalPoint π hπ hex hp ha q ≫ exceptionalToSpecial π hπ hex hp ha q =
      Cross.endpoint k ≫ resolveRightEnd π hπ hex hp ha q := by
  apply (cancel_mono (pullback.fst ((resolve π hπ hex hp ha (q + 1)).map ≫ base) residueBase)).mp
  simp only [Category.assoc, exceptionalToSpecial_fst, rightExceptionalPoint, pullback.lift_fst]
@[reassoc (attr := simp)] lemma leftExceptionalPoint_base (q : ℕ) :
    leftExceptionalPoint π hπ hex hp ha q ≫
      pullback.snd (resolve π hπ hex hp ha (q + 1)).map (originalNode hπ q) = 𝟙 _ :=
        pullback.lift_snd ..
@[reassoc (attr := simp)] lemma rightExceptionalPoint_base (q : ℕ) :
    rightExceptionalPoint π hπ hex hp ha q ≫
      pullback.snd (resolve π hπ hex hp ha (q + 1)).map (originalNode hπ q) = 𝟙 _ :=
        pullback.lift_snd ..

/-- The left end has exactly its reduced origin as exceptional pullback. -/
lemma leftExceptionalPoint_isPullback (q : ℕ) :
    IsPullback (Cross.endpoint k) (leftExceptionalPoint π hπ hex hp ha q)
      (resolveLeftEnd π hπ hex hp ha q) (exceptionalToSpecial π hπ hex hp ha q) := by
  let p := pullback.fst ((resolve π hπ hex hp ha (q + 1)).map ≫ base) residueBase ≫
    (resolve π hπ hex hp ha (q + 1)).map
  have : IsClosedImmersion (resolveLeftEnd π hπ hex hp ha q ≫ p) := by
    dsimp [p]
    rw [resolveLeftEnd_target]
    exact IsClosedImmersion.spec_of_surjective _ (residueLeftHom_surjective _
      (residue_uniformizer_pow hπ q))
  have H : IsPullback (Cross.endpoint k) (𝟙 (Spec (.of k)))
      (resolveLeftEnd π hπ hex hp ha q ≫ p) (originalNode hπ q) :=
    IsPullback.of_vert_isIso_mono ⟨by
      simpa only [p, Category.id_comp] using (leftEndpoint_target π hπ hex hp ha q)⟩
  rw [← leftExceptionalPoint_base π hπ hex hp ha q] at H
  exact H.of_bot (leftExceptionalPoint_special π hπ hex hp ha q).symm
    (exceptionalToSpecial_square π hπ hex hp ha q)

/-- The right end has exactly its reduced origin as exceptional pullback. -/
lemma rightExceptionalPoint_isPullback (q : ℕ) :
    IsPullback (Cross.endpoint k) (rightExceptionalPoint π hπ hex hp ha q)
      (resolveRightEnd π hπ hex hp ha q) (exceptionalToSpecial π hπ hex hp ha q) := by
  let p := pullback.fst ((resolve π hπ hex hp ha (q + 1)).map ≫ base) residueBase ≫
    (resolve π hπ hex hp ha (q + 1)).map
  have : IsClosedImmersion (resolveRightEnd π hπ hex hp ha q ≫ p) := by
    dsimp [p]
    rw [resolveRightEnd_target]
    exact IsClosedImmersion.spec_of_surjective _ (residueRightHom_surjective _
      (residue_uniformizer_pow hπ q))
  have H : IsPullback (Cross.endpoint k) (𝟙 (Spec (.of k)))
      (resolveRightEnd π hπ hex hp ha q ≫ p) (originalNode hπ q) :=
    IsPullback.of_vert_isIso_mono ⟨by
      simpa only [p, Category.id_comp] using (rightEndpoint_target π hπ hex hp ha q)⟩
  rw [← rightExceptionalPoint_base π hπ hex hp ha q] at H
  exact H.of_bot (rightExceptionalPoint_special π hπ hex hp ha q).symm
    (exceptionalToSpecial_square π hπ hex hp ha q)

@[reassoc] lemma leftExceptionalPoint_two :
    Reciprocal.zeroSection k ≫ exceptionalP1 π hπ hex hp ha 1 0 =
      leftExceptionalPoint π hπ hex hp ha 1 := by
  apply (cancel_mono (exceptionalToSpecial π hπ hex hp ha 1)).mp
  simp only [Category.assoc, exceptionalP1_special, leftExceptionalPoint_special]
  exact (twoLeftEnd_intersection_isPullback hπ (OneStepBlowup.ofFamilies π 0 hex hp ha)).w.symm

@[reassoc] lemma rightExceptionalPoint_two :
    Reciprocal.infinitySection k ≫ exceptionalP1 π hπ hex hp ha 1 0 =
      rightExceptionalPoint π hπ hex hp ha 1 := by
  apply (cancel_mono (exceptionalToSpecial π hπ hex hp ha 1)).mp
  simp only [Category.assoc, exceptionalP1_special, rightExceptionalPoint_special]
  exact (twoRightEnd_intersection_isPullback hπ (OneStepBlowup.ofFamilies π 0 hex hp ha)).w.symm

@[reassoc] lemma leftExceptionalPoint_step (q : ℕ) :
    Reciprocal.infinitySection k ≫ exceptionalP1 π hπ hex hp ha (q + 2) 0 =
      leftExceptionalPoint π hπ hex hp ha (q + 2) := by
  apply (cancel_mono (exceptionalToSpecial π hπ hex hp ha (q + 2))).mp
  simp only [Category.assoc, exceptionalP1_special, leftExceptionalPoint_special]
  exact (resolveLeftEnd_newP1_isPullback π hπ hex hp ha q).w.symm

@[reassoc] lemma rightExceptionalPoint_step (q : ℕ) :
    Reciprocal.infinitySection k ≫ exceptionalP1 π hπ hex hp ha (q + 2) (Fin.last q).succ =
      rightExceptionalPoint π hπ hex hp ha (q + 2) := by
  apply (cancel_mono (exceptionalToSpecial π hπ hex hp ha (q + 2))).mp
  simp only [Category.assoc, exceptionalP1_special, rightExceptionalPoint_special,
    interiorComponent, Fin.cases_succ, Fin.lastCases_last]
  exact (resolveRightEnd_newP1_isPullback π hπ hex hp ha q).w.symm

/-- Each left attachment point is on its actual labelled end P1 when n > 1. -/
lemma leftExceptionalPoint_on_P1 : ∀ q, 0 < q → ∃ (i : Fin q)
    (s : Spec (.of k) ⟶ projectiveP1 k),
    s ≫ exceptionalP1 π hπ hex hp ha q i = leftExceptionalPoint π hπ hex hp ha q
  | 0, h => False.elim (Nat.not_lt_zero _ h)
  | 1, _ => ⟨0, Reciprocal.zeroSection k, leftExceptionalPoint_two π hπ hex hp ha⟩
  | q + 2, _ => ⟨0, Reciprocal.infinitySection k, leftExceptionalPoint_step π hπ hex hp ha q⟩

/-- The right endpoint keeps its separately labelled actual attachment map. -/
lemma rightExceptionalPoint_on_P1 : ∀ q, 0 < q → ∃ (i : Fin q)
    (s : Spec (.of k) ⟶ projectiveP1 k),
    s ≫ exceptionalP1 π hπ hex hp ha q i = rightExceptionalPoint π hπ hex hp ha q
  | 0, h => False.elim (Nat.not_lt_zero _ h)
  | 1, _ => ⟨0, Reciprocal.infinitySection k, rightExceptionalPoint_two π hπ hex hp ha⟩
  | q + 2, _ => ⟨(Fin.last q).succ, Reciprocal.infinitySection k, rightExceptionalPoint_step π hπ
    hex hp ha q⟩

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeExceptionalEndFibres


section NodeChainCoverage

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) (hπ : Irreducible π)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (ha : BlowupAffineAtlas.{u})
local notation "k" => IsLocalRing.ResidueField R

/-- Every actual point of the resolved special fibre belongs to one of its two
constructed affine end curves or to one of the constructed projective curves. -/
theorem resolve_components_cover : ∀ q (z : sourceSpecialFibre (resolve π hπ hex hp ha (q + 1))),
    z ∈ Set.range (resolveLeftEnd π hπ hex hp ha q) ∨
      z ∈ Set.range (resolveRightEnd π hπ hex hp ha q) ∨
        ∃ i : Fin q, z ∈ Set.range (interiorComponent π hπ hex hp ha q i)
  | 0, z => by
    rcases base_ends_cover π hπ z with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  | 1, z => by
    rcases two_components_cover hπ (OneStepBlowup.ofFamilies π 0 hex hp ha) z with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨0, h⟩)
    · exact Or.inr (Or.inl h)
  | q + 2, z => by
    let B := OneStepBlowup.ofFamilies π (q + 1) hex hp ha
    let E := resolve π hπ hex hp ha (q + 1)
    rcases fibre_three_charts_cover B hπ E z with ⟨x, rfl⟩ | ⟨x, rfl⟩ | ⟨x, rfl⟩
    · rcases resolve_components_cover q x with ⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨i, a, rfl⟩
      · right; right
        refine ⟨0, chart k 0 a, ?_⟩
        exact congr($(resolveLeftNewP1_old_chart π hπ hex hp ha q) a)
      · right; right
        refine ⟨(Fin.last q).succ, chart k 0 a, ?_⟩
        simpa only [interiorComponent, Fin.cases_succ, Fin.lastCases_last, Scheme.Hom.comp_apply,
          B, E] using
          congr($(resolveRightNewP1_old_chart π hπ hex hp ha q) a)
      · right; right
        refine ⟨i.castSucc.succ, a, ?_⟩
        simp only [interiorComponent, Fin.cases_succ, Fin.lastCases_castSucc]
        rfl
    · rcases outer_branches_cover hπ x with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · exact Or.inl ⟨a, rfl⟩
      · right; right
        refine ⟨0, chart k 1 a, ?_⟩
        exact congr($(resolveLeftNewP1_new_chart π hπ hex hp ha q) a)
    · rcases outer_branches_cover hπ x with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · exact Or.inr (Or.inl ⟨a, rfl⟩)
      · right; right
        refine ⟨(Fin.last q).succ, chart k 1 a, ?_⟩
        simpa only [interiorComponent, Fin.cases_succ, Fin.lastCases_last, Scheme.Hom.comp_apply,
          B, E] using
          congr($(resolveRightNewP1_new_chart π hπ hex hp ha q) a)

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeChainCoverage


section NodeFibreSeparation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme.PowerNode.BlowupOverlaps AlgebraicGeometry.Scheme.Blowup.Coordinates
  AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {π : R} (hπ : Irreducible π)
local notation "k" => IsLocalRing.ResidueField R

/-- The literal left/right overlap, displayed in either outer coordinate chart. -/
def outerOverlapOpen (π : R) (m : ℕ) : (Spec (.of (PlaneNode.Ring π))).Opens :=
  PrimeSpectrum.basicOpen (outerRatio π m)

section ArbitraryStep
variable {m : ℕ} (B : OneStepBlowup.Data π m) (E : Data π m)

lemma stepLeft_preimage_right :
    stepLeftChart B hπ E ⁻¹' Set.range (stepRightChart B hπ E) =
      (outerOverlapOpen π m : Set (Spec (.of (PlaneNode.Ring π)))) := by
  rw [range_snd_of_isPullback (stepRightChart_isPullback B hπ E)]
  change (stepLeftChart B hπ E ≫ stepToBlowup B hπ E) ⁻¹' Set.range (rightChartMap B.atlas hπ) = _
  rw [stepLeftChart_toBlowup]
  rw [chart_preimage_of_overlap (awayMap (outerRatio π m)) (leftChartMap B.atlas hπ)
    (rightChartMap B.atlas hπ) (outer_range hπ B.atlas)]
  exact PrimeSpectrum.localization_away_comap_range _ _

lemma stepRight_preimage_left :
    stepRightChart B hπ E ⁻¹' Set.range (stepLeftChart B hπ E) =
      (outerOverlapOpen π m : Set (Spec (.of (PlaneNode.Ring π)))) := by
  rw [range_snd_of_isPullback (stepLeftChart_isPullback B hπ E)]
  change (stepRightChart B hπ E ≫ stepToBlowup B hπ E) ⁻¹' Set.range (leftChartMap B.atlas hπ) = _
  rw [stepRightChart_toBlowup]
  rw [chart_preimage_of_overlap (awayMap (outerRatio π m)) (rightChartMap B.atlas hπ)
    (leftChartMap B.atlas hπ)
    (overlap_range B.atlas (generator π m 2) (generator π m 0)
      (dvrRightReesEquiv π hπ m).toRingEquiv (dvrLeftReesEquiv π hπ m).toRingEquiv
      (outerRatio π m) (right_left_ratio π hπ m))]
  exact PrimeSpectrum.localization_away_comap_range _ _

lemma leftFibre_preimage_right :
    leftFibreChart B hπ E ⁻¹' Set.range (rightFibreChart B hπ E) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))) residueBase ⁻¹'
        (outerOverlapOpen π m : Set (Spec (.of (PlaneNode.Ring π)))) := by
  dsimp only [leftFibreChart, rightFibreChart, sourceSpecialFibre, outerFibre]
  rw [fibreChart_preimage_range, stepLeft_preimage_right]

lemma rightFibre_preimage_left :
    rightFibreChart B hπ E ⁻¹' Set.range (leftFibreChart B hπ E) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))) residueBase ⁻¹'
        (outerOverlapOpen π m : Set (Spec (.of (PlaneNode.Ring π)))) := by
  dsimp only [leftFibreChart, rightFibreChart, sourceSpecialFibre, outerFibre]
  rw [fibreChart_preimage_range, stepRight_preimage_left]

/-- Each strict-transform A1 end is entirely outside the resolved middle chart. -/
lemma stepLeftEnd_preimage_middle_empty :
    stepLeftEnd hπ B E ⁻¹' Set.range (middleFibreChart B hπ E) = ∅ := by
  change outerEndBranch hπ ⁻¹' (leftFibreChart B hπ E ⁻¹' Set.range (middleFibreChart B hπ E)) = _
  rw [leftFibre_preimage_middle]
  change (outerEndBranch hπ ≫
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))) residueBase) ⁻¹'
      (uniformizerVOpen π : Set (Spec (.of (PlaneNode.Ring π)))) = _
  rw [outerEndBranch_fst]
  ext x
  change (residueLeftHom π (residue_uniformizer hπ)) (PlaneNode.V π) ∉ x.asIdeal ↔ False
  simp [residueLeftHom]

lemma stepRightEnd_preimage_middle_empty :
    stepRightEnd hπ B E ⁻¹' Set.range (middleFibreChart B hπ E) = ∅ := by
  change outerEndBranch hπ ⁻¹' (rightFibreChart B hπ E ⁻¹' Set.range (middleFibreChart B hπ E)) = _
  rw [rightFibre_preimage_middle]
  change (outerEndBranch hπ ≫
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))) residueBase) ⁻¹'
      (uniformizerVOpen π : Set (Spec (.of (PlaneNode.Ring π)))) = _
  rw [outerEndBranch_fst]
  ext x
  change (residueLeftHom π (residue_uniformizer hπ)) (PlaneNode.V π) ∉ x.asIdeal ↔ False
  simp [residueLeftHom]

lemma leftEnd_middle_disjoint : Disjoint (Set.range (stepLeftEnd hπ B E))
    (Set.range (middleFibreChart B hπ E)) := by
  rw [Set.disjoint_left]
  rintro z ⟨a, rfl⟩ hz
  have h : a ∈ stepLeftEnd hπ B E ⁻¹' Set.range (middleFibreChart B hπ E) := hz
  rw [stepLeftEnd_preimage_middle_empty] at h
  exact h

lemma rightEnd_middle_disjoint : Disjoint (Set.range (stepRightEnd hπ B E))
    (Set.range (middleFibreChart B hπ E)) := by
  rw [Set.disjoint_left]
  rintro z ⟨a, rfl⟩ hz
  have h : a ∈ stepRightEnd hπ B E ⁻¹' Set.range (middleFibreChart B hπ E) := hz
  rw [stepRightEnd_preimage_middle_empty] at h
  exact h
end ArbitraryStep

/-- For a positive middle exponent, the actual outer-overlap equation specializes to zero. -/
lemma positive_outerRatio_specialization (m : ℕ) :
    nodeSpecializeAt π (0 : k) (residue_uniformizer hπ) (outerRatio π (m + 1)) = 0 := by
  simp only [outerRatio, map_mul, map_pow, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply R k (PlaneNode.Ring (0 : k)), residue_uniformizer hπ, map_zero,
    zero_pow (Nat.succ_ne_zero m), zero_mul]

set_option maxHeartbeats 400000 in
-- Identifying the actual outer residue pullback with the cross uses about
-- 239000 heartbeats; allow finite headroom for this individual comparison.
lemma positive_outerFibre_overlap_empty (hπ : Irreducible π) (m : ℕ) :
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))) (residueBase (R
      := R)) ⁻¹'
      (outerOverlapOpen π (m + 1) : Set (Spec (.of (PlaneNode.Ring π)))) = ∅ := by
  ext x
  obtain ⟨z, rfl⟩ := (outerCrossIso hπ).hom.surjective x
  change ((outerCrossIso hπ).hom ≫
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))) residueBase) z ∈
      (outerOverlapOpen π (m + 1) : Set (Spec (.of (PlaneNode.Ring π)))) ↔ False
  rw [outerCrossIso_hom_fst]
  change nodeSpecializeAt π (0 : k) (residue_uniformizer hπ) (outerRatio π (m + 1)) ∉ z.asIdeal ↔
    False
  rw [positive_outerRatio_specialization hπ m]
  simp

section PositiveMiddle
variable (m : ℕ) (B : OneStepBlowup.Data π (m + 1)) (E : Data π (m + 1))

lemma positive_leftFibre_preimage_right_empty :
    leftFibreChart B hπ E ⁻¹' Set.range (rightFibreChart B hπ E) = ∅ := by
  rw [leftFibre_preimage_right, positive_outerFibre_overlap_empty hπ]

lemma positive_rightFibre_preimage_left_empty :
    rightFibreChart B hπ E ⁻¹' Set.range (leftFibreChart B hπ E) = ∅ := by
  rw [rightFibre_preimage_left, positive_outerFibre_overlap_empty hπ]

/-- The two actual outer residue charts are disjoint for every positive middle exponent. -/
lemma positive_outer_fibres_disjoint : Disjoint (Set.range (leftFibreChart B hπ E))
    (Set.range (rightFibreChart B hπ E)) := by
  rw [Set.disjoint_left]
  rintro z ⟨a, rfl⟩ hz
  have h : a ∈ leftFibreChart B hπ E ⁻¹' Set.range (rightFibreChart B hπ E) := hz
  rw [positive_leftFibre_preimage_right_empty] at h
  exact h
end PositiveMiddle

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeFibreSeparation
