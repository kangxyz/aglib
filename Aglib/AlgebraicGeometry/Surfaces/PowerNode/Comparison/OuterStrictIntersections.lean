/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.PullbackTransport
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.NativeStrictIntersections
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.StrictExceptionalFibres
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.NodeChainIntersections

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.OuterStrictIntersections`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`e4ce1d2668c7410a99f61780a0c958a084b3b9dfa0dcb65aa3c72ffbd4881eb1`.
Full source-present outer/strict scheme intersections, original local endpoints and their actual
  global pullback squares. Original DVR, Cartier/chart and birational-locus inputs remain explicit.
  The actual etale curve-chart suppliers provide regularity and dimension internally.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode WeierstrassCurve
open AlgebraicGeometry.Scheme.FunctionField AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre

open _root_.AlgebraicGeometry.Scheme (SmoothClosedPointDimension SmoothFieldRegularity)

/-!
# Outer projective-line pullbacks and strict exceptional ends

This module preserves the conditional interfaces and source-coverage boundaries
recorded in the individual sections below.
-/

section WeierstrassOuterP1Pullbacks

/-! The full actual pullback of each exceptional P1 to either retained first
outer chart. The local P1, its chart projection, and the residue base are fixed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (m : ℕ)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 2)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "S" => initialState M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ
local notation "C" => initialChart M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ
local notation "T" => originalRun M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ hex hp hatlas
  hbc
local notation "BG" => State.blowup S hex
local notation "BC" => State.commonBlowup S hex
local notation "D" => OneStepBlowup.ofFamilies π m hex hp hatlas
local notation "A" => runAfterFirstMap hex hp hatlas hbc m S
local notation "g" => modification M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ hex hp
  hatlas hbc
local notation "r" => Resolution.residueBase (R := R)
local notation "E" => Resolution.resolve π hπ hex hp hatlas (m + 2)
local notation "P" => originalExceptionalP1 M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc
local notation "N" => Resolution.interiorComponent π hπ hex hp hatlas (m + 1)

variable (side : Bool) (j : Fin (m + 1))
local notation "Z" => Resolution.firstOuterP1 π hπ hex hp hatlas m side j
local notation "zP" => Resolution.firstOuterP1ToP1 π hπ hex hp hatlas m side j
local notation "zN" => Resolution.firstOuterP1ToNode π hπ hex hp hatlas m side j
local notation "Nbase" => Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))
local notation "pC" => originalP1FirstCommon M π hπ m a ha he ρ hρ hex hp hatlas hbc j
local notation "pN" => N j ≫ pullback.fst (Resolution.Data.map E ≫ Resolution.base) r ≫
  Resolution.stepToBlowup D hπ (Resolution.resolve π hπ hex hp hatlas m)
local notation "O" => firstStrictOuterSpecial M π hπ m a ha he ρ hρ hex hp hatlas hbc side
local notation "oG" => firstStrictOuterSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc side
local notation "oN" => firstStrictOuterToNode M π hπ m a ha he ρ hρ hex hp hatlas hbc side

/-- The local P1 chart lifts into the same retained first outer chart. -/
def originalOuterP1ToRetained : Z ⟶ firstRetainedOuter hex hp hatlas hbc m S side :=
  AlgebraicGeometry.Scheme.Pullback.OuterTransport.retainedLift pC (Chart.Step.toNode C D BC)
    (Chart.Step.toGlobal C BG BC) pN
    (P j ≫ pullback.fst (g ≫ structureMap W) r ≫ A)
    (Resolution.firstOuterChartMap D hπ side)
    (originalP1FirstCommon_node M π hπ m a ha he ρ hρ hex hp hatlas hbc j)
    (zN ≫ pullback.fst Nbase r) zP
    (Resolution.firstOuterP1_firstBlowup_square π hπ hex hp hatlas m side j)
    A (P j ≫ pullback.fst (g ≫ structureMap W) r) (by simp only [Category.assoc])
    (originalP1FirstCommon_global_square M π hπ m a ha he ρ hρ hex hp hatlas hbc j)

lemma originalOuterP1ToRetained_square :
    IsPullback (originalOuterP1ToRetained M π hπ m a ha he ρ hρ hex hp hatlas hbc side j)
      zP (firstRetainedOuterMap hex hp hatlas hbc m S side)
      (P j ≫ pullback.fst (g ≫ structureMap W) r) :=
  AlgebraicGeometry.Scheme.Pullback.OuterTransport.retainedLift_square ..

@[reassoc] lemma originalOuterP1ToRetained_node :
    originalOuterP1ToRetained M π hπ m a ha he ρ hρ hex hp hatlas hbc side j ≫
      firstRetainedOuterToNode hex hp hatlas hbc m S side = zN ≫ pullback.fst Nbase r := by
  have H : originalOuterP1ToRetained M π hπ m a ha he ρ hρ hex hp hatlas hbc side j ≫
      firstRetainedOuterToRaw hex hp hatlas hbc m S side =
      AlgebraicGeometry.Scheme.Pullback.OuterTransport.commonLift pC (Chart.Step.toNode C D BC) pN
        (Resolution.firstOuterChartMap D hπ side)
        (originalP1FirstCommon_node M π hπ m a ha he ρ hρ hex hp hatlas hbc j)
        (zN ≫ pullback.fst Nbase r) zP
        (Resolution.firstOuterP1_firstBlowup_square π hπ hex hp hatlas m side j) :=
    AlgebraicGeometry.Scheme.Pullback.OuterTransport.retainedLift_snd ..
  rw [firstRetainedOuterToNode, ← Category.assoc, H]
  exact AlgebraicGeometry.Scheme.Pullback.OuterTransport.commonLift_snd ..

lemma firstStrictOuterSpecial_square :
    IsPullback (firstOuterSpecialToRetained hex hp hatlas hbc m S side (structureMap W))
      oG (firstRetainedOuterMap hex hp hatlas hbc m S side)
      (pullback.fst (g ≫ structureMap W) r) := by
  exact (IsPullback.of_hasPullback (firstRetainedOuterMap hex hp hatlas hbc m S side)
    (pullback.fst (A ≫ (BG).map ≫ structureMap W) r)).of_iso
    (Iso.refl _) (Iso.refl _)
    (firstMiddleSpecialFibreIso M π hπ m a ha he ρ hρ hex hp hatlas hbc) (Iso.refl _)
    (by simp) (by simp [firstStrictOuterSpecialMap]) (by simp)
    (by simp only [Iso.refl_hom, Category.comp_id, firstMiddleSpecialFibreIso_hom_fst])

/-- Exact common exceptional identity, through the retained and residue charts. -/
def originalOuterP1ToSpecial : Z ⟶ O :=
  AlgebraicGeometry.Scheme.Pullback.OuterTransport.squareLift
    (firstStrictOuterSpecial_square M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
    (originalOuterP1ToRetained M π hπ m a ha he ρ hρ hex hp hatlas hbc side j) zP (P j)
    (originalOuterP1ToRetained_square M π hπ m a ha he ρ hρ hex hp hatlas hbc side j)

lemma originalOuterP1ToSpecial_square :
    IsPullback (originalOuterP1ToSpecial M π hπ m a ha he ρ hρ hex hp hatlas hbc side j)
      zP oG (P j) := AlgebraicGeometry.Scheme.Pullback.OuterTransport.squareLift_square ..

@[reassoc] lemma originalOuterP1ToSpecial_retained :
    originalOuterP1ToSpecial M π hπ m a ha he ρ hρ hex hp hatlas hbc side j ≫
      firstOuterSpecialToRetained hex hp hatlas hbc m S side (structureMap W) =
        originalOuterP1ToRetained M π hπ m a ha he ρ hρ hex hp hatlas hbc side j :=
  AlgebraicGeometry.Scheme.Pullback.OuterTransport.squareLift_fst ..

@[reassoc] lemma originalOuterP1ToSpecial_global :
    originalOuterP1ToSpecial M π hπ m a ha he ρ hρ hex hp hatlas hbc side j ≫ oG = zP ≫ P j :=
  AlgebraicGeometry.Scheme.Pullback.OuterTransport.squareLift_snd ..

@[reassoc] lemma originalOuterP1ToSpecial_node :
    originalOuterP1ToSpecial M π hπ m a ha he ρ hρ hex hp hatlas hbc side j ≫ oN = zN := by
  have hb : P j ≫ pullback.snd (g ≫ structureMap W) r =
      AlgebraicGeometry.Scheme.ProjectiveLine.structureMap (ResidueField R) :=
    originalExceptionalP1_base M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc j
  have hnb : N j ≫ pullback.snd ((E).map ≫ Resolution.base) r =
      AlgebraicGeometry.Scheme.ProjectiveLine.structureMap (ResidueField R) :=
    Resolution.interiorComponent_base π hπ hex hp hatlas (m + 1) j
  have hchart : Resolution.firstOuterFibreChart D hπ
      (Resolution.resolve π hπ hex hp hatlas m) side ≫
      pullback.snd ((E).map ≫ Resolution.base) r = pullback.snd Nbase r :=
    Resolution.firstOuterFibreChart_base D hπ (Resolution.resolve π hπ hex hp hatlas m) side
  apply pullback.hom_ext
  · rw [Category.assoc, firstOuterSpecialToNode_fst,
      originalOuterP1ToSpecial_retained_assoc, originalOuterP1ToRetained_node]
  · rw [Category.assoc, ← firstStrictOuterSpecialMap_base,
      originalOuterP1ToSpecial_global_assoc, hb]
    have H := congrArg (· ≫ pullback.snd ((E).map ≫ Resolution.base) r)
      (IsPullback.of_hasPullback (N j) (Resolution.firstOuterFibreChart D hπ
        (Resolution.resolve π hπ hex hp hatlas m) side)).w
    simpa only [Category.assoc, hnb, hchart] using H

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassOuterP1Pullbacks




section WeierstrassStrictOuterSupport

/-! Exhaustivity of actual strict/exceptional intersections, using the full
puncture, retained outer, and retained middle cover of the SAME final fibre. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (m : ℕ)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 2)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "S" => initialState M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ
local notation "C" => initialChart M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ
local notation "T" => originalRun M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ hex hp hatlas
  hbc
local notation "BG" => State.blowup S hex
local notation "BC" => State.commonBlowup S hex
local notation "D" => OneStepBlowup.ofFamilies π m hex hp hatlas
local notation "A" => runAfterFirstMap hex hp hatlas hbc m S
local notation "g" => modification M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ hex hp
  hatlas hbc
local notation "r" => Resolution.residueBase (R := R)
local notation "E" => Resolution.resolve π hπ hex hp hatlas (m + 2)
local notation "P" => originalExceptionalP1 M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc
local notation "N" => Resolution.interiorComponent π hπ hex hp hatlas (m + 1)

variable (side : Bool) (j : Fin (m + 1))
local notation "Z" => Resolution.firstOuterP1 π hπ hex hp hatlas m side j
local notation "zP" => Resolution.firstOuterP1ToP1 π hπ hex hp hatlas m side j
local notation "zN" => Resolution.firstOuterP1ToNode π hπ hex hp hatlas m side j
local notation "Nbase" => Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))
local notation "pC" => originalP1FirstCommon M π hπ m a ha he ρ hρ hex hp hatlas hbc j
local notation "pN" => N j ≫ pullback.fst (Resolution.Data.map E ≫ Resolution.base) r ≫
  Resolution.stepToBlowup D hπ (Resolution.resolve π hπ hex hp hatlas m)
local notation "O" => firstStrictOuterSpecial M π hπ m a ha he ρ hρ hex hp hatlas hbc side
local notation "oG" => firstStrictOuterSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc side
local notation "oN" => firstStrictOuterToNode M π hπ m a ha he ρ hρ hex hp hatlas hbc side

local notation "i" => strictTransformInclusion M π hπ (m + 2) (Nat.succ_pos (m + 1))
  a ha he ρ hρ hex hp hatlas hbc
local notation "nO" => Resolution.firstOuterFibreChart D hπ
  (Resolution.resolve π hπ hex hp hatlas m) side

lemma strictExceptional_preimage_on_outer :
    (zP ≫ P j) ⁻¹' Set.range i = zN ⁻¹' Set.range (Resolution.outerEndBranch hπ) :=
  AlgebraicGeometry.Scheme.Pullback.ChartTransport.strict_preimage_on_chart i oG oN
    (Resolution.outerEndBranch hπ)
    (firstStrictOuterPullbackIso M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
    (firstStrictOuterPullbackIso_hom_fst M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
    nO (N j) (originalOuterP1ToSpecial M π hπ m a ha he ρ hρ hex hp hatlas hbc side j)
    zP zN (P j)
    (originalOuterP1ToSpecial_square M π hπ m a ha he ρ hρ hex hp hatlas hbc side j)
    (originalOuterP1ToSpecial_node M π hπ m a ha he ρ hρ hex hp hatlas hbc side j)
    (IsPullback.of_hasPullback (N j) nO).flip

lemma strictExceptional_in_outer_local (p : AlgebraicGeometry.Scheme.ProjectiveLine.projectiveP1
  (ResidueField R))
    (hs : P j p ∈ Set.range i) (ho : P j p ∈ Set.range oG) :
    N j p ∈ Set.range (Resolution.outerEndBranch hπ ≫ nO) := by
  have hpre : p ∈ Set.range zP := by
    rw [Scheme.Pullback.Transport.range_eq_preimage_of_isPullback
      (originalOuterP1ToSpecial_square M π hπ m a ha he ρ hρ hex hp hatlas hbc side j).flip]
    exact ho
  obtain ⟨z,hz⟩ := hpre
  have hs' : z ∈ (zP ≫ P j) ⁻¹' Set.range i := by
    change P j (zP z) ∈ Set.range i
    rw [hz]
    exact hs
  rw [strictExceptional_preimage_on_outer] at hs'
  obtain ⟨t,ht⟩ := hs'
  refine ⟨t, ?_⟩
  change nO (Resolution.outerEndBranch hπ t) = N j p
  rw [ht]
  have H := congrArg (fun f => f z) (IsPullback.of_hasPullback (N j) nO).w
  change N j (zP z) = nO (zN z) at H
  rw [hz] at H
  exact H.symm

/-- Any actual strict/P1 point belongs to one of the two original local ends.
The proof excludes the full middle chart and the full original puncture. -/
lemma strictExceptional_local_ends (p : AlgebraicGeometry.Scheme.ProjectiveLine.projectiveP1
  (ResidueField R))
    (hs : P j p ∈ Set.range i) :
    N j p ∈ Set.range (Resolution.resolveLeftEnd π hπ hex hp hatlas (m + 1)) ∨
      N j p ∈ Set.range (Resolution.resolveRightEnd π hπ hex hp hatlas (m + 1)) := by
  rcases strictPunctured_firstSpecialCharts_cover M π hπ m a ha he ρ hρ hex hp hatlas hbc (P j p)
    with hv | hl | hr | hm
  · exfalso
    obtain ⟨v,hv⟩ := hv
    have hd := strictPunctured_original_disjoint M π hπ (m + 2) (Nat.succ_pos (m + 1))
      a ha he ρ hρ hex hp hatlas hbc
    apply Set.disjoint_left.mp hd ⟨v,rfl⟩
    refine ⟨AlgebraicGeometry.Scheme.ProjectiveLine.structureMap (ResidueField R) p, ?_⟩
    have H := congrArg (fun f => f p)
      (originalExceptionalP1_original M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc j)
    have hv' := congrArg
      (fun z : finalSpecialFibre M π hπ (m + 2) (Nat.succ_pos (m + 1))
          a ha he ρ hρ hex hp hatlas hbc =>
        (pullback.fst (g ≫ structureMap W)
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g) z) hv
    exact H.symm.trans hv'.symm
  · exact Or.inl (strictExceptional_in_outer_local M π hπ m a ha he ρ hρ
      hex hp hatlas hbc false j p hs hl)
  · exact Or.inr (strictExceptional_in_outer_local M π hπ m a ha he ρ hρ
      hex hp hatlas hbc true j p hs hr)
  · exact False.elim (Set.disjoint_left.mp
      (Scheme.isEmpty_pullback_iff.mp
        (firstMiddleStrictPullback_empty M π hπ m a ha he ρ hρ hex hp hatlas hbc)) hs hm)

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassStrictOuterSupport


section WeierstrassStrictOuterPoints

/-! Actual point lifts to the same strict closure, with exact scheme squares.
The local intersection and open-containment arguments are discharged below for
both extreme exceptional P1s; all other strict/P1 intersections are empty. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (m : ℕ)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 2)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "S" => initialState M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ
local notation "C" => initialChart M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ
local notation "T" => originalRun M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ hex hp hatlas
  hbc
local notation "BG" => State.blowup S hex
local notation "BC" => State.commonBlowup S hex
local notation "D" => OneStepBlowup.ofFamilies π m hex hp hatlas
local notation "A" => runAfterFirstMap hex hp hatlas hbc m S
local notation "g" => modification M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ hex hp
  hatlas hbc
local notation "r" => Resolution.residueBase (R := R)
local notation "E" => Resolution.resolve π hπ hex hp hatlas (m + 2)
local notation "P" => originalExceptionalP1 M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc
local notation "N" => Resolution.interiorComponent π hπ hex hp hatlas (m + 1)

variable (side : Bool) (j : Fin (m + 1))
local notation "Z" => Resolution.firstOuterP1 π hπ hex hp hatlas m side j
local notation "zP" => Resolution.firstOuterP1ToP1 π hπ hex hp hatlas m side j
local notation "zN" => Resolution.firstOuterP1ToNode π hπ hex hp hatlas m side j
local notation "Nbase" => Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))
local notation "pC" => originalP1FirstCommon M π hπ m a ha he ρ hρ hex hp hatlas hbc j
local notation "pN" => N j ≫ pullback.fst (Resolution.Data.map E ≫ Resolution.base) r ≫
  Resolution.stepToBlowup D hπ (Resolution.resolve π hπ hex hp hatlas m)
local notation "O" => firstStrictOuterSpecial M π hπ m a ha he ρ hρ hex hp hatlas hbc side
local notation "oG" => firstStrictOuterSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc side
local notation "oN" => firstStrictOuterToNode M π hπ m a ha he ρ hρ hex hp hatlas hbc side

local notation "i" => strictTransformInclusion M π hπ (m + 2) (Nat.succ_pos (m + 1))
  a ha he ρ hρ hex hp hatlas hbc
local notation "nO" => Resolution.firstOuterFibreChart D hπ
  (Resolution.resolve π hπ hex hp hatlas m) side

variable {Q : Scheme.{u}} (s : Q ⟶ Resolution.Cross.line (ResidueField R))
  (t : Q ⟶ AlgebraicGeometry.Scheme.ProjectiveLine.projectiveP1 (ResidueField R))
  (H : IsPullback s t (Resolution.outerEndBranch hπ ≫
    Resolution.firstOuterFibreChart (OneStepBlowup.ofFamilies π m hex hp hatlas) hπ
      (Resolution.resolve π hπ hex hp hatlas m) side)
    (Resolution.interiorComponent π hπ hex hp hatlas (m + 1) j))

/-- Transports the given outer-branch intersection morphism into the global strict transform. -/
def strictOuterPoint : Q ⟶ strictTransform M π hπ (m + 2) (Nat.succ_pos (m + 1))
    a ha he ρ hρ hex hp hatlas hbc :=
  AlgebraicGeometry.Scheme.Pullback.ChartTransport.strictPoint i oG oN (Resolution.outerEndBranch
    hπ)
    (firstStrictOuterPullbackIso M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
    nO (N j) (originalOuterP1ToSpecial M π hπ m a ha he ρ hρ hex hp hatlas hbc side j)
    zP zN (IsPullback.of_hasPullback (N j) nO).flip
    (originalOuterP1ToSpecial_node M π hπ m a ha he ρ hρ hex hp hatlas hbc side j) s t H

lemma strictOuterPoint_isPullback
    (hs : P j ⁻¹' Set.range i ⊆ Set.range zP) :
    IsPullback (strictOuterPoint M π hπ m a ha he ρ hρ hex hp hatlas hbc side j s t H)
      t i (P j) :=
  AlgebraicGeometry.Scheme.Pullback.ChartTransport.strictPoint_square i oG oN
    (Resolution.outerEndBranch hπ)
    (firstStrictOuterPullbackIso M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
    (firstStrictOuterPullbackIso_hom_fst M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
    nO (N j) (originalOuterP1ToSpecial M π hπ m a ha he ρ hρ hex hp hatlas hbc side j)
    zP zN (IsPullback.of_hasPullback (N j) nO).flip (P j)
    (originalOuterP1ToSpecial_square M π hπ m a ha he ρ hρ hex hp hatlas hbc side j)
    (originalOuterP1ToSpecial_node M π hπ m a ha he ρ hρ hex hp hatlas hbc side j) s t H hs

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassStrictOuterPoints


section WeierstrassStrictExceptionalEnds

/-! Exact strict-closure/extreme-P1 attachments at thickness at least three.
The first/last exceptional projections are literally interiorStart/interiorFinish. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (m : ℕ)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 3)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "k" => ResidueField R
local notation "P" => originalExceptionalP1 M π hπ (m + 2) a ha he ρ hρ hex hp hatlas hbc
local notation "i" => strictTransformInclusion M π hπ (m + 3) (Nat.succ_pos (m + 2)) a ha he ρ hρ
  hex hp hatlas hbc
local notation "N" => Resolution.interiorComponent π hπ hex hp hatlas (m + 2)
local notation "D" => OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas
local notation "E" => Resolution.resolve π hπ hex hp hatlas (m + 1)
local notation "L" => Resolution.resolveLeftEnd π hπ hex hp hatlas (m + 2)
local notation "Rₑ" => Resolution.resolveRightEnd π hπ hex hp hatlas (m + 2)
local notation "last" => (Fin.last (m + 1) : Fin (m + 2))

lemma strictExceptional_left_chart_support :
    P 0 ⁻¹' Set.range i ⊆ Set.range
      (Resolution.firstOuterP1ToP1 π hπ hex hp hatlas (m + 1) false 0) := by
  intro p hs
  rcases strictExceptional_local_ends M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc 0 p hs with hl
    | hr
  · rw [Scheme.Pullback.range_fst]
    exact Scheme.Pullback.Fibre.morphism_range_comp_subset _ _ hl
  · have hne : (0 : Fin (m + 2)) ≠ (Fin.last m).succ := by
      intro h
      have hval : (0 : ℕ) = m + 1 := congrArg Fin.val h
      omega
    exact False.elim (Set.disjoint_left.mp
      (Resolution.rightEnd_interior_disjoint_of_ne π hπ hex hp hatlas m 0 hne) hr ⟨p,rfl⟩)

lemma strictExceptional_right_chart_support :
    P last ⁻¹' Set.range i ⊆ Set.range
      (Resolution.firstOuterP1ToP1 π hπ hex hp hatlas (m + 1) true last) := by
  intro p hs
  rcases strictExceptional_local_ends M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc last p hs with
    hl | hr
  · have hne : last ≠ 0 := by
      intro h
      have hval : m + 1 = 0 := congrArg Fin.val h
      omega
    exact False.elim (Set.disjoint_left.mp
      (Resolution.leftEnd_interior_disjoint_of_ne π hπ hex hp hatlas m last hne) hl ⟨p,rfl⟩)
  · rw [Scheme.Pullback.range_fst]
    exact Scheme.Pullback.Fibre.morphism_range_comp_subset _ _ hr

lemma localLeftStrictAttachment_square :
    IsPullback (Resolution.Cross.endpoint k) (Resolution.interiorStart (R := R) (m + 2) 0)
      (Resolution.outerEndBranch hπ ≫ Resolution.firstOuterFibreChart D hπ E false) (N 0) := by
  exact Resolution.chainAdjacent_isPullback π hπ hex hp hatlas (Resolution.ChainAdjacent.stepLeft m)

lemma localRightStrictAttachment_square :
    IsPullback (Resolution.Cross.endpoint k) (Resolution.interiorFinish (R := R) (m + 2) last)
      (Resolution.outerEndBranch hπ ≫ Resolution.firstOuterFibreChart D hπ E true) (N last) := by
  exact (Resolution.chainAdjacent_isPullback π hπ hex hp hatlas
    (Resolution.ChainAdjacent.stepRight m)).flip

/-- The left outer attachment point on the strict transform, obtained from the first interior
component. -/
def originalLeftStrictClosurePoint : Spec (.of k) ⟶ strictTransform M π hπ (m + 3)
    (Nat.succ_pos (m + 2)) a ha he ρ hρ hex hp hatlas hbc :=
  strictOuterPoint M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc false 0
    (Resolution.Cross.endpoint k) (Resolution.interiorStart (R := R) (m + 2) 0)
    (localLeftStrictAttachment_square π hπ m hex hp hatlas)

/-- The right outer attachment point on the strict transform, obtained from the last interior
component. -/
def originalRightStrictClosurePoint : Spec (.of k) ⟶ strictTransform M π hπ (m + 3)
    (Nat.succ_pos (m + 2)) a ha he ρ hρ hex hp hatlas hbc :=
  strictOuterPoint M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc true last
    (Resolution.Cross.endpoint k) (Resolution.interiorFinish (R := R) (m + 2) last)
    (localRightStrictAttachment_square π hπ m hex hp hatlas)

lemma originalLeftStrictClosurePoint_isPullback :
    IsPullback (originalLeftStrictClosurePoint M π hπ m a ha he ρ hρ hex hp hatlas hbc)
      (Resolution.interiorStart (R := R) (m + 2) 0) i (P 0) :=
  strictOuterPoint_isPullback M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc false 0
    (Resolution.Cross.endpoint k) (Resolution.interiorStart (R := R) (m + 2) 0)
    (localLeftStrictAttachment_square π hπ m hex hp hatlas)
    (strictExceptional_left_chart_support M π hπ m a ha he ρ hρ hex hp hatlas hbc)

lemma originalRightStrictClosurePoint_isPullback :
    IsPullback (originalRightStrictClosurePoint M π hπ m a ha he ρ hρ hex hp hatlas hbc)
      (Resolution.interiorFinish (R := R) (m + 2) last) i (P last) :=
  strictOuterPoint_isPullback M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc true last
    (Resolution.Cross.endpoint k) (Resolution.interiorFinish (R := R) (m + 2) last)
    (localRightStrictAttachment_square π hπ m hex hp hatlas)
    (strictExceptional_right_chart_support M π hπ m a ha he ρ hρ hex hp hatlas hbc)

lemma strictClosureExceptionalInterior_disjoint (j : Fin (m + 2)) (h0 : j ≠ 0) (hlast : j ≠ last) :
    Disjoint (Set.range i) (Set.range (P j)) := by
  apply Set.disjoint_left.mpr
  rintro _ hs ⟨p,rfl⟩
  rcases strictExceptional_local_ends M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc j p hs with hl
    | hr
  · exact Set.disjoint_left.mp (Resolution.leftEnd_interior_disjoint_of_ne π hπ hex hp hatlas m j
    h0) hl ⟨p,rfl⟩
  · exact Set.disjoint_left.mp (Resolution.rightEnd_interior_disjoint_of_ne π hπ hex hp hatlas m j
    hlast) hr ⟨p,rfl⟩

lemma strictClosureExceptionalInterior_empty (j : Fin (m + 2)) (h0 : j ≠ 0) (hlast : j ≠ last) :
    IsEmpty (pullback i (P j) : Scheme.{u}) :=
  Scheme.isEmpty_pullback_iff.mpr (strictClosureExceptionalInterior_disjoint M π hπ m a ha he ρ hρ
    hex hp hatlas hbc j h0 hlast)

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassStrictExceptionalEnds


section WeierstrassStrictExceptionalIntersections

/-! Exact pairwise strict/P1 intersections on the SAME resolved special fibre,
with the original strict P1 map and original exceptional P1 maps. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
  AlgebraicGeometry.Scheme.RegularityDescent
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (m : ℕ)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 3)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "k" => ResidueField R
local notation "P" => originalExceptionalP1 M π hπ (m + 2) a ha he ρ hρ hex hp hatlas hbc
local notation "i" => strictTransformInclusion M π hπ (m + 3) (Nat.succ_pos (m + 2)) a ha he ρ hρ
  hex hp hatlas hbc
local notation "N" => Resolution.interiorComponent π hπ hex hp hatlas (m + 2)
local notation "D" => OneStepBlowup.ofFamilies π (m + 1) hex hp hatlas
local notation "E" => Resolution.resolve π hπ hex hp hatlas (m + 1)
local notation "L" => Resolution.resolveLeftEnd π hπ hex hp hatlas (m + 2)
local notation "Rₑ" => Resolution.resolveRightEnd π hπ hex hp hatlas (m + 2)
local notation "last" => (Fin.last (m + 1) : Fin (m + 2))

variable (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (hext : NormalProperCurveGenericExtension.{u})
  (hdvr : AlgebraicGeometry.Scheme.ProperBirationalDVRIsomorphismLocus.{u})
local notation "e" => strictNormalizationIsoPositive M π hπ (m + 1) a ha he ρ hρ
  hex hp hatlas hbc hx hy hext hdvr
local notation "f" => strictP1ToFinal M π hπ (m + 3) (Nat.succ_pos (m + 2))
  a ha he ρ hρ hex hp hatlas hbc hx hy hext
local notation "base" => pullback.snd
  (modification M π hπ (m + 3) (Nat.succ_pos (m + 2)) a ha he ρ hρ hex hp hatlas hbc ≫
    structureMap W)
  (Resolution.residueBase (R := R))

/-- The left strict-transform attachment expressed on the projective line through the supplied
normalization isomorphism. -/
def originalLeftStrictPoint : Spec (.of k) ⟶ AlgebraicGeometry.Scheme.ProjectiveLine.projectiveP1
  k :=
  originalLeftStrictClosurePoint M π hπ m a ha he ρ hρ hex hp hatlas hbc ≫ (e).inv

/-- The right strict-transform attachment expressed on the projective line through the supplied
normalization isomorphism. -/
def originalRightStrictPoint : Spec (.of k) ⟶ AlgebraicGeometry.Scheme.ProjectiveLine.projectiveP1
  k :=
  originalRightStrictClosurePoint M π hπ m a ha he ρ hρ hex hp hatlas hbc ≫ (e).inv

lemma originalLeftStrictPoint_isPullback :
    IsPullback (originalLeftStrictPoint M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy hext hdvr)
      (Resolution.interiorStart (R := R) (m + 2) 0) f (P 0) := by
  apply (originalLeftStrictClosurePoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc).of_iso
    (Iso.refl _) (e).symm (Iso.refl _) (Iso.refl _)
  · simp only [originalLeftStrictPoint, Iso.refl_hom, Iso.symm_hom, Category.id_comp]
  · simp
  · change i ≫ 𝟙 _ = (e).inv ≫ ((e).hom ≫ i)
    simp
  · simp

lemma originalRightStrictPoint_isPullback :
    IsPullback (originalRightStrictPoint M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy hext hdvr)
      (Resolution.interiorFinish (R := R) (m + 2) last) f (P last) := by
  apply (originalRightStrictClosurePoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc).of_iso
    (Iso.refl _) (e).symm (Iso.refl _) (Iso.refl _)
  · simp only [originalRightStrictPoint, Iso.refl_hom, Iso.symm_hom, Category.id_comp]
  · simp
  · change i ≫ 𝟙 _ = (e).inv ≫ ((e).hom ≫ i)
    simp
  · simp

@[reassoc] lemma originalLeftStrictPoint_over :
    originalLeftStrictPoint M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy hext hdvr ≫ AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k = 𝟙
        _ := by
  have H := congrArg (· ≫ base)
    (originalLeftStrictPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy hext hdvr).w
  have hf : f ≫ base = AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k :=
    strictP1ToFinal_over M π hπ (m + 3) (Nat.succ_pos (m + 2))
      a ha he ρ hρ hex hp hatlas hbc hx hy hext
  have hpj : P 0 ≫ base = AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k :=
    originalExceptionalP1_base M π hπ (m + 2) a ha he ρ hρ hex hp hatlas hbc 0
  simpa only [Category.assoc, hf, hpj, Resolution.interiorStart_over] using H

@[reassoc] lemma originalRightStrictPoint_over :
    originalRightStrictPoint M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy hext hdvr ≫ AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k = 𝟙
        _ := by
  have H := congrArg (· ≫ base)
    (originalRightStrictPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy hext hdvr).w
  have hf : f ≫ base = AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k :=
    strictP1ToFinal_over M π hπ (m + 3) (Nat.succ_pos (m + 2))
      a ha he ρ hρ hex hp hatlas hbc hx hy hext
  have hpj : P last ≫ base = AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k :=
    originalExceptionalP1_base M π hπ (m + 2) a ha he ρ hρ hex hp hatlas hbc last
  simpa only [Category.assoc, hf, hpj, Resolution.interiorFinish_over] using H

lemma strictExceptionalInterior_empty (j : Fin (m + 2)) (h0 : j ≠ 0) (hlast : j ≠ last) :
    IsEmpty (pullback f (P j) : Scheme.{u}) := by
  apply Scheme.isEmpty_pullback_iff.mpr
  exact (strictClosureExceptionalInterior_disjoint M π hπ m a ha he ρ hρ hex hp hatlas hbc j h0
    hlast).mono_left
    (Scheme.Pullback.Fibre.morphism_range_comp_subset _ _)

/-- Actual scheme pullback, not only a singleton support assertion. -/
def strictFirstExceptionalIntersectionIso : pullback f (P 0) ≅ Spec (.of k) :=
  (originalLeftStrictPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
    hx hy hext hdvr).isoPullback.symm

/-- Actual scheme pullback, with the literal final exceptional section. -/
def strictLastExceptionalIntersectionIso : pullback f (P last) ≅ Spec (.of k) :=
  (originalRightStrictPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
    hx hy hext hdvr).isoPullback.symm

@[reassoc] lemma strictFirstExceptionalIntersectionIso_inv_exceptional :
    (strictFirstExceptionalIntersectionIso M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy hext hdvr).inv ≫ pullback.snd f (P 0) =
        Resolution.interiorStart (R := R) (m + 2) 0 :=
  (originalLeftStrictPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
    hx hy hext hdvr).isoPullback_hom_snd

@[reassoc] lemma strictLastExceptionalIntersectionIso_inv_exceptional :
    (strictLastExceptionalIntersectionIso M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy hext hdvr).inv ≫ pullback.snd f (P last) =
        Resolution.interiorFinish (R := R) (m + 2) last :=
  (originalRightStrictPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
    hx hy hext hdvr).isoPullback_hom_snd

@[reassoc] lemma strictFirstExceptionalIntersectionIso_inv_strict :
    (strictFirstExceptionalIntersectionIso M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy hext hdvr).inv ≫ pullback.fst f (P 0) =
        originalLeftStrictPoint M π hπ m a ha he ρ hρ hex hp hatlas hbc
          hx hy hext hdvr :=
  (originalLeftStrictPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
    hx hy hext hdvr).isoPullback_hom_fst

@[reassoc] lemma strictLastExceptionalIntersectionIso_inv_strict :
    (strictLastExceptionalIntersectionIso M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy hext hdvr).inv ≫ pullback.fst f (P last) =
        originalRightStrictPoint M π hπ m a ha he ρ hρ hex hp hatlas hbc
          hx hy hext hdvr :=
  (originalRightStrictPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
    hx hy hext hdvr).isoPullback_hom_fst

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassStrictExceptionalIntersections
