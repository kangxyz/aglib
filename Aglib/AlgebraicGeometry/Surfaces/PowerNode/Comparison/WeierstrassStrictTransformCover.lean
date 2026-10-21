/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.StrictTransformCover
public import
  Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.WeierstrassStrictTransformClosure

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.StrictTransformCover`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`2c487b89f159bc11256bc673307f85a0d31dc8d17c6943d661a9e98c9bc2881f`.
All original Weierstrass sections source240–635,1080–1205,1313–1394: actual retained first charts,
  exact middle contraction/exclusion, genuine component inventory and whole-fibre coverage. The
  initial structural triangle is proved directly from the existing actual chart maps; no
  additional compatibility record or model is supplied.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre

section WeierstrassFirstMiddleExclusion

/-! For every original thickness m + 2, the ENTIRE first middle chart retained
through the actual Run has an etale map to the SAME final special fibre.
Its full scheme-valued contraction is the original residue point, so its
pullback of the actual strict transform is empty without any extra premise. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (m : ℕ)
  (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 2)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})

local notation "S₀" => initialState M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ
local notation "C₀" => initialChart M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ
local notation "BG" => State.blowup S₀ hex
local notation "BC" => State.commonBlowup S₀ hex
local notation "D" => OneStepBlowup.ofFamilies π m hex hp hatlas
local notation "f" => runAfterFirstMap hex hp hatlas hbc m S₀
local notation "g" => modification M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp
  hatlas hbc
local notation "r" => Resolution.residueBase (R := R)
local notation "F" => finalSpecialFibre M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex
  hp hatlas hbc
local notation "V" => strictPuncturedOpen M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ
  hex hp hatlas hbc

/-- Exact factorization of the original modification, not a replacement model. -/
@[reassoc] lemma originalAfterFirst_triangle : f ≫ (BG).map = g := by
  rw [runAfterFirstMap_triangle]
  simp only [modification, originalRun, Run.toOriginal, initialState, Category.comp_id]

/-- The initial pointed chart's structural triangle over the original DVR. -/
lemma firstMiddle_initial_base :
    (C₀).toGlobal ≫ structureMap W = (C₀).toNode ≫ Resolution.base := by
  have H : ProjectiveNodeBlowup.commonToProjective M ≫ structureMap W =
      M.toPowerNodeScheme (π ^ (m + 2)) a ha ≫ Resolution.base := by
    rw [ProjectiveNodeBlowup.commonToProjective, Category.assoc, affineChart_structure,
      M.original_structure_triangle, Resolution.base, M.power_structure_triangle]
  change (_ ≫ ProjectiveNodeBlowup.commonToProjective M) ≫ structureMap W =
    (_ ≫ M.toPowerNodeScheme (π ^ (m + 2)) a ha) ≫ Resolution.base
  rw [Category.assoc, H, Category.assoc]

/-- Only the exact original modification equality changes the presentation
of this literal pullback; the source model and residue field remain fixed. -/
def firstMiddleSpecialFibreIso :
    Chart.Step.laterSpecialFibre C₀ BG (structureMap W) f ≅ F :=
  pullback.congrHom (by rw [← Category.assoc, originalAfterFirst_triangle]) rfl

@[reassoc (attr := simp)] lemma firstMiddleSpecialFibreIso_hom_fst :
    (firstMiddleSpecialFibreIso M π hπ m a ha he ρ hρ hex hp hatlas hbc).hom ≫
      pullback.fst (g ≫ structureMap W) r =
        pullback.fst (f ≫ (BG).map ≫ structureMap W) r := by
  simp [firstMiddleSpecialFibreIso, pullback.congrHom_hom]

@[reassoc (attr := simp)] lemma firstMiddleSpecialFibreIso_hom_snd :
    (firstMiddleSpecialFibreIso M π hπ m a ha he ρ hρ hex hp hatlas hbc).hom ≫
      pullback.snd (g ≫ structureMap W) r =
        pullback.snd (f ≫ (BG).map ≫ structureMap W) r := by
  simp [firstMiddleSpecialFibreIso, pullback.congrHom_hom]

/-- The full retained first middle, with no selection of an integral component. -/
abbrev firstMiddleSpecial : Scheme.{u} :=
  Chart.Step.laterMiddleSpecial C₀ D BG BC (structureMap W) f

/-- Actual chart map into the same final special fibre used by strictTransform. -/
def firstMiddleSpecialMap :
    firstMiddleSpecial M π hπ m a ha he ρ hρ hex hp hatlas hbc ⟶ F :=
  Chart.Step.laterMiddleSpecialMap C₀ D BG BC (structureMap W) f ≫
    (firstMiddleSpecialFibreIso M π hπ m a ha he ρ hρ hex hp hatlas hbc).hom

lemma firstMiddleSpecialMap_etale :
    Etale (firstMiddleSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc) := by
  let := Chart.Step.laterMiddleSpecialMap_etale C₀ D BG BC hbc (structureMap W) f
  dsimp only [firstMiddleSpecialMap]
  infer_instance

/-- The structural map to the SAME original residue field. -/
abbrev firstMiddleSpecialBase :
    firstMiddleSpecial M π hπ m a ha he ρ hρ hex hp hatlas hbc ⟶
      Spec (.of (ResidueField R)) :=
  Chart.Step.laterMiddleSpecialBase C₀ D BG BC (structureMap W) f

@[reassoc] lemma firstMiddleSpecialMap_base :
    firstMiddleSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc ≫
      pullback.snd (g ≫ structureMap W) r =
        firstMiddleSpecialBase M π hπ m a ha he ρ hρ hex hp hatlas hbc := by
  simp only [firstMiddleSpecialMap, Category.assoc, firstMiddleSpecialFibreIso_hom_snd]
  rfl

/-- Exact contraction of every scheme-valued point of the full retained middle
chart, including thickness two, to the original Weierstrass residue point. -/
@[reassoc] lemma firstMiddleSpecial_contracts :
    firstMiddleSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc ≫
      pullback.fst (g ≫ structureMap W) r ≫ g =
        firstMiddleSpecialBase M π hπ m a ha he ρ hρ hex hp hatlas hbc ≫
          residueNodeMap W x y he := by
  simp only [firstMiddleSpecialMap, Category.assoc, firstMiddleSpecialFibreIso_hom_fst_assoc]
  rw [← originalAfterFirst_triangle M π hπ m a ha he ρ hρ hex hp hatlas hbc]
  exact Chart.Step.laterMiddleSpecial_contracts C₀ D BG BC (structureMap W)
    (firstMiddle_initial_base M π hπ m a ha he ρ hρ) f

/-- No additional avoidance, flatness, component, or cover hypothesis:
the actual strict transform has empty pullback on the entire first middle. -/
lemma firstMiddleStrictPullback_empty :
    IsEmpty (pullback (C := Scheme.{u})
      (strictTransformInclusion M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp
        hatlas hbc)
      (firstMiddleSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc)) := by
  let := firstMiddleSpecialMap_etale M π hπ m a ha he ρ hρ hex hp hatlas hbc
  let : IsIntegral (Scheme.Opens.toScheme (X := F) V) :=
    strictPunctured_integral M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp hatlas
      hbc
  let : IsLocallyNoetherian F :=
    finalSpecialFibre_noetherian M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp
      hatlas hbc
  let : QuasiCompact (Scheme.Opens.ι (X := F) V) := by infer_instance
  exact AlgebraicGeometry.Scheme.Hom.Image.flatClosurePullback_empty_of_contraction
    (Scheme.Opens.ι (X := F) V)
    (firstMiddleSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc)
    (pullback.fst (g ≫ structureMap W) r ≫ g) (residueNodeMap W x y he)
    (firstMiddleSpecialBase M π hπ m a ha he ρ hρ hex hp hatlas hbc)
    (firstMiddleSpecial_contracts M π hπ m a ha he ρ hρ hex hp hatlas hbc)
    (strictPunctured_original_disjoint M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex
      hp hatlas hbc)

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassFirstMiddleExclusion

section WeierstrassExceptionalMiddleTransport

/-! Actual P1 middle points transported through the full exceptional comparison
into the SAME final special fibre. Empty strict-middle pullback proves genuine
noncontainment in the global strict transform, without dimension assumptions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
open AlgebraicGeometry.Scheme.ProjectiveLine (projectiveP1)
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
local notation "k" => ResidueField R
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
local notation "F" => finalSpecialFibre M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ hex hp
  hatlas hbc
local notation "middle" => firstMiddleSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc
local notation "strict" => strictTransformInclusion M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he
  ρ hρ hex hp hatlas hbc
local notation "P" => originalExceptionalP1 M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc

/-- The literal first-middle pullback range inside the actual final fibre. -/
lemma firstMiddleSpecialMap_range : Set.range middle =
    (pullback.fst (g ≫ structureMap W) r ≫ A) ⁻¹'
      Set.range (Chart.Step.middleToGlobal C D BG BC) := by
  have H : IsPullback
      (pullback.fst (Chart.Step.laterMiddleMap C D BG BC A)
        (pullback.fst (A ≫ (BG).map ≫ structureMap W) r))
      middle (Chart.Step.laterMiddleMap C D BG BC A)
      (pullback.fst (g ≫ structureMap W) r) := by
    exact (IsPullback.of_hasPullback (Chart.Step.laterMiddleMap C D BG BC A)
      (pullback.fst (A ≫ (BG).map ≫ structureMap W) r)).of_iso
      (Iso.refl _) (Iso.refl _)
      (firstMiddleSpecialFibreIso M π hπ m a ha he ρ hρ hex hp hatlas hbc) (Iso.refl _)
      (by simp) (by simp [firstMiddleSpecialMap]) (by simp)
      (by simp only [Iso.refl_hom, Category.comp_id, firstMiddleSpecialFibreIso_hom_fst])
  refine (Scheme.Pullback.Fibre.pullback_range_snd H).trans ?_
  simp only [Chart.Step.laterMiddleMap, Scheme.Pullback.range_fst]
  rfl

/-- The actual exceptional P1 mapped into the SAME first common blowup. -/
def originalP1FirstCommon (j : Fin (m + 1)) : projectiveP1 k ⟶ (BC).Y :=
  Run.commonExceptionalMap T (Resolution.exceptionalP1 π hπ hex hp hatlas (m + 1) j) ≫
    Run.firstCommonToBlowup T (by omega)

@[reassoc] lemma originalP1FirstCommon_global (j : Fin (m + 1)) :
    originalP1FirstCommon M π hπ m a ha he ρ hρ hex hp hatlas hbc j ≫
      Chart.Step.toGlobal C BG BC =
    P j ≫ pullback.fst (g ≫ structureMap W) r ≫ A := by
  have Hfirst : Run.firstCommonToBlowup T (by omega) ≫ Chart.Step.toGlobal C BG BC =
      (T).fullCommonToGlobal ≫ A := Run.firstCommonToBlowup_global m S T
  have Hspecial : originalExceptionalToSpecial M π hπ (m + 2) (Nat.succ_pos (m + 1))
      a ha he ρ hρ hex hp hatlas hbc ≫ pullback.fst (g ≫ structureMap W) r =
      Run.exceptionalToGlobal T :=
    originalExceptionalToSpecial_fst M π hπ (m + 2) (Nat.succ_pos (m + 1)) a ha he ρ hρ hex hp
      hatlas hbc
  have Hp : P j ≫ pullback.fst (g ≫ structureMap W) r =
      Run.globalExceptionalMap T (Resolution.exceptionalP1 π hπ hex hp hatlas (m + 1) j) := by
    have H := congrArg (Resolution.exceptionalP1 π hπ hex hp hatlas (m + 1) j ≫ ·) Hspecial
    simpa only [Category.assoc, originalExceptionalP1, Run.globalExceptionalMap_eq,
      Run.exceptionalComponent, Run.exceptionalToGlobal] using H
  rw [originalP1FirstCommon, Category.assoc, Hfirst]
  change Run.globalExceptionalMap T (Resolution.exceptionalP1 π hπ hex hp hatlas (m + 1) j) ≫ _ = _
  simpa only [Category.assoc] using congrArg (· ≫ A) Hp.symm

@[reassoc] lemma originalP1FirstCommon_node (j : Fin (m + 1)) :
    originalP1FirstCommon M π hπ m a ha he ρ hρ hex hp hatlas hbc j ≫
      Chart.Step.toNode C D BC =
    Resolution.interiorComponent π hπ hex hp hatlas (m + 1) j ≫
      pullback.fst ((E).map ≫ Resolution.base) r ≫
      Resolution.stepToBlowup D hπ (Resolution.resolve π hπ hex hp hatlas m) := by
  have Hfirst : Run.firstCommonToBlowup T (by omega) ≫ Chart.Step.toNode C D BC =
      Run.fullNodeComparison T ≫ Resolution.stepToBlowup D hπ
        (Resolution.resolve π hπ hex hp hatlas m) := Run.firstCommonToBlowup_node m S T
  have Hnode : Run.commonExceptionalMap T (Resolution.exceptionalP1 π hπ hex hp hatlas (m + 1) j) ≫
      Run.fullNodeComparison T =
      Resolution.interiorComponent π hπ hex hp hatlas (m + 1) j ≫
        pullback.fst ((E).map ≫ Resolution.base) r := by
    exact (Run.commonExceptionalMap_node T
      (Resolution.exceptionalP1 π hπ hex hp hatlas (m + 1) j)).trans (pullback.lift_fst ..)
  rw [originalP1FirstCommon, Category.assoc, Hfirst, ← Category.assoc, Hnode]
  simp only [Category.assoc]

/-- Local middle membership is transferred through an existing actual source
map and the literal common-chart pullback, not through an arbitrary etale lift. -/
lemma originalExceptionalP1_point_in_firstMiddle (j : Fin (m + 1)) (p : projectiveP1 k)
    (hmid : (Resolution.interiorComponent π hπ hex hp hatlas (m + 1) j ≫
      pullback.fst ((E).map ≫ Resolution.base) r ≫
      Resolution.stepToBlowup D hπ (Resolution.resolve π hπ hex hp hatlas m)) p ∈
      Set.range (BlowupAtlas.middleChartMap (D).atlas hπ)) :
    P j p ∈ Set.range middle := by
  let c := originalP1FirstCommon M π hπ m a ha he ρ hρ hex hp hatlas hbc j
  have hc : c p ∈ Set.range (Chart.Step.middleToCommon C D BC) := by
    change c p ∈ Set.range (pullback.fst (Chart.Step.toNode C D BC)
      (BlowupAtlas.middleChartMap (D).atlas hπ))
    rw [Scheme.Pullback.range_fst]
    change (Chart.Step.toNode C D BC) (c p) ∈
      Set.range (BlowupAtlas.middleChartMap (D).atlas hπ)
    rw [← Scheme.Hom.comp_apply]
    rw [show c = originalP1FirstCommon M π hπ m a ha he ρ hρ hex hp hatlas hbc j from rfl,
      originalP1FirstCommon_node]
    exact hmid
  obtain ⟨z,hz⟩ := hc
  rw [firstMiddleSpecialMap_range]
  refine ⟨z,?_⟩
  change (Chart.Step.middleToCommon C D BC ≫ Chart.Step.toGlobal C BG BC) z =
    (P j ≫ pullback.fst (g ≫ structureMap W) r ≫ A) p
  rw [← originalP1FirstCommon_global]
  exact congrArg (Chart.Step.toGlobal C BG BC) hz

/-- Every actual exceptional P1 has a point outside the actual global strict
transform; the proof uses its same-final-fibre first-middle image. -/
lemma originalExceptionalP1_not_subset_strict (j : Fin (m + 1)) :
    ¬ Set.range (P j) ⊆ Set.range strict := by
  intro H
  obtain ⟨p,hpoint⟩ := Resolution.exceptionalP1_firstBlowup_meets_middle π hπ hex hp hatlas m j
  have hm := originalExceptionalP1_point_in_firstMiddle M π hπ m a ha he ρ hρ hex hp hatlas hbc j
    p hpoint
  obtain ⟨z,hz⟩ := hm
  have hs : middle z ∈ Set.range strict := by
    rw [hz]
    exact H ⟨p,rfl⟩
  have hz' : z ∈ middle ⁻¹' Set.range strict := hs
  rw [← Scheme.Pullback.range_snd] at hz'
  obtain ⟨w,_⟩ := hz'
  let := firstMiddleStrictPullback_empty M π hπ m a ha he ρ hρ hex hp hatlas hbc
  exact isEmptyElim w

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassExceptionalMiddleTransport

section WeierstrassResolvedComponentInventory

/-! Actual maximal components of the whole same-source resolved special fibre.
Their equivalence and total count are derived from the geometric cover and
proved noncontainment, without a numerical or component-classification input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (q : ℕ)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (q + 1)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "Y" => finalSpecialFibre M π hπ (q + 1) (Nat.succ_pos _) a ha he ρ hρ hex hp hatlas
  hbc
local notation "strict" => strictTransformInclusion M π hπ (q + 1) (Nat.succ_pos _) a ha he ρ hρ
  hex hp hatlas hbc
local notation "P" => originalExceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc

lemma originalExceptionalP1_not_subset_strict_positive (hq : 0 < q) (j : Fin q) :
    ¬ Set.range (P j) ⊆ Set.range strict := by
  cases q with
  | zero => exact False.elim (Nat.not_lt_zero _ hq)
  | succ m =>
    exact originalExceptionalP1_not_subset_strict M π hπ m a ha he ρ hρ hex hp hatlas hbc j

/-- Each constructed exceptional P1 is maximal in the WHOLE final special
fibre, not merely maximal inside the exceptional subscheme. -/
lemma originalExceptionalP1_mem_irreducibleComponents (hq : 0 < q) (j : Fin q) :
    Set.range (P j) ∈ irreducibleComponents Y := by
  refine ⟨originalExceptionalP1_range_irreducible M π hπ q a ha he ρ hρ hex hp hatlas hbc j,?_⟩
  intro s hs hjs
  rcases irreducible_subset_strict_or_exceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc hq hs
      with H | ⟨l,H⟩
  · exact False.elim (originalExceptionalP1_not_subset_strict_positive M π hπ q a ha he ρ hρ hex
    hp hatlas hbc hq j (hjs.trans H))
  · by_cases hjl : j = l
    · subst l
      exact H
    · exact False.elim (originalExceptionalP1_pairwise_not_subset M π hπ q a ha he ρ hρ hex hp
      hatlas hbc j l hjl (hjs.trans H))

/-- None is the actual reduced strict closure; some j is the actual jth P1. -/
def resolvedComponentRange : Option (Fin q) → Set Y
  | none => Set.range strict
  | some j => Set.range (P j)

lemma resolvedComponentRange_mem (hq : 0 < q) (j : Option (Fin q)) :
    resolvedComponentRange M π hπ q a ha he ρ hρ hex hp hatlas hbc j ∈ irreducibleComponents Y := by
  cases j with
  | none =>
    exact strictTransform_mem_irreducibleComponents M π hπ q a ha he ρ hρ hex hp hatlas hbc hq
  | some j =>
    exact originalExceptionalP1_mem_irreducibleComponents M π hπ q a ha he ρ hρ hex hp hatlas
      hbc hq j

lemma resolvedComponentRange_injective (hq : 0 < q) :
    Function.Injective (resolvedComponentRange M π hπ q a ha he ρ hρ hex hp hatlas hbc) := by
  intro j l H
  cases j with
  | none =>
    cases l with
    | none => rfl
    | some l => exact False.elim (strict_not_subset_originalExceptionalP1 M π hπ q a ha he ρ hρ
      hex hp hatlas hbc l H.le)
  | some j =>
    cases l with
    | none => exact False.elim (originalExceptionalP1_not_subset_strict_positive M π hπ q a ha he
      ρ hρ hex hp hatlas hbc hq j H.le)
    | some l =>
      congr 1
      by_contra hjl
      exact originalExceptionalP1_pairwise_not_subset M π hπ q a ha he ρ hρ hex hp hatlas hbc j l
        hjl H.le

lemma resolved_irreducibleComponents_eq (hq : 0 < q) :
    irreducibleComponents Y = Set.range (resolvedComponentRange M π hπ q a ha he ρ hρ hex hp
      hatlas hbc) := by
  ext s
  constructor
  · intro hs
    rcases irreducible_subset_strict_or_exceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc hq
      hs.1
        with H | ⟨j,H⟩
    · refine ⟨none,?_⟩
      exact (Set.Subset.antisymm H (hs.2
        (strictTransform_mem_irreducibleComponents M π hπ q a ha he ρ hρ hex hp hatlas hbc hq).1
          H)).symm
    · refine ⟨some j,?_⟩
      exact (Set.Subset.antisymm H (hs.2
        (originalExceptionalP1_range_irreducible M π hπ q a ha he ρ hρ hex hp hatlas hbc j) H)).symm
  · rintro ⟨j,rfl⟩
    exact resolvedComponentRange_mem M π hπ q a ha he ρ hρ hex hp hatlas hbc hq j

/-- The exhaustive component equivalence of the actual resolved special fibre. -/
def resolvedComponentEquiv (hq : 0 < q) : Option (Fin q) ≃ irreducibleComponents Y :=
  Equiv.ofBijective (fun j => ⟨resolvedComponentRange M π hπ q a ha he ρ hρ hex hp hatlas hbc j,
    resolvedComponentRange_mem M π hπ q a ha he ρ hρ hex hp hatlas hbc hq j⟩) (by
    constructor
    · intro j l H
      exact resolvedComponentRange_injective M π hπ q a ha he ρ hρ hex hp hatlas hbc hq (congrArg
        Subtype.val H)
    · intro s
      obtain ⟨j,hj⟩ := (resolved_irreducibleComponents_eq M π hπ q a ha he ρ hρ hex hp hatlas hbc
        hq).le s.property
      exact ⟨j,Subtype.ext hj⟩)

lemma resolvedComponentEquiv_range (hq : 0 < q) (j : Option (Fin q)) :
    (resolvedComponentEquiv M π hπ q a ha he ρ hρ hex hp hatlas hbc hq j).val =
      resolvedComponentRange M π hπ q a ha he ρ hρ hex hp hatlas hbc j := rfl

/-- For exponent n=q + 1>1, the actual entire resolved special fibre has n
components. The count is a conclusion of the geometric component equivalence. -/
lemma resolved_irreducibleComponents_card (hq : 0 < q) :
    Nat.card (irreducibleComponents Y) = q + 1 := by
  rw [← Nat.card_congr (resolvedComponentEquiv M π hπ q a ha he ρ hρ hex hp hatlas hbc hq)]
  simp

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassResolvedComponentInventory

section WeierstrassRetainedOuterStrict

/-! Both entire first outer charts of the SAME final Weierstrass residue fibre.
The strict transform pulls back to the FULL actual end-branch pullback, with
its projection preserved. No replacement component or affine-line is supplied. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (m : ℕ)
  (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 2)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u}) (side : Bool)
local notation "S₀" => initialState M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ
local notation "C₀" => initialChart M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ
local notation "g" => modification M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp
  hatlas hbc
local notation "r" => Resolution.residueBase (R := R)
local notation "F" => finalSpecialFibre M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex
  hp hatlas hbc
local notation "V" => strictPuncturedOpen M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ
  hex hp hatlas hbc
local notation "i" => strictTransformInclusion M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ
  hρ hex hp hatlas hbc

/-- The retained first outer special-fibre chart for the original Weierstrass resolution run. -/
abbrev firstStrictOuterSpecial : Scheme.{u} :=
  firstOuterSpecial hex hp hatlas hbc m S₀ side (structureMap W)

/-- The retained first outer special-fibre chart mapped into the final Weierstrass special fibre. -/
def firstStrictOuterSpecialMap :
    firstStrictOuterSpecial M π hπ m a ha he ρ hρ hex hp hatlas hbc side ⟶ F :=
  firstOuterSpecialMap hex hp hatlas hbc m S₀ side (structureMap W) ≫
    (firstMiddleSpecialFibreIso M π hπ m a ha he ρ hρ hex hp hatlas hbc).hom

/-- The retained first outer special-fibre chart mapped to the initial common chart. -/
abbrev firstStrictOuterToCommon :
    firstStrictOuterSpecial M π hπ m a ha he ρ hρ hex hp hatlas hbc side ⟶ (C₀).C :=
  firstOuterSpecialToCommon hex hp hatlas hbc m S₀ side (structureMap W)

/-- The retained first outer special-fibre chart mapped to the outer node fibre. -/
abbrev firstStrictOuterToNode :
    firstStrictOuterSpecial M π hπ m a ha he ρ hρ hex hp hatlas hbc side ⟶
      Resolution.outerFibre (π := π) :=
  firstOuterSpecialToNode hex hp hatlas hbc m S₀ side (structureMap W)
    (firstMiddle_initial_base M π hπ m a ha he ρ hρ)

lemma firstStrictOuterSpecialMap_etale :
    Etale (firstStrictOuterSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc side) := by
  let := firstOuterSpecialMap_etale hex hp hatlas hbc m S₀ side (structureMap W)
  dsimp only [firstStrictOuterSpecialMap]
  infer_instance

lemma firstStrictOuterToNode_etale :
    Etale (firstStrictOuterToNode M π hπ m a ha he ρ hρ hex hp hatlas hbc side) :=
  firstOuterSpecialToNode_etale hex hp hatlas hbc m S₀ side (structureMap W)
    (firstMiddle_initial_base M π hπ m a ha he ρ hρ)

@[reassoc] lemma firstStrictOuterSpecialMap_base :
    firstStrictOuterSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc side ≫
      pullback.snd (g ≫ structureMap W) r =
        firstStrictOuterToNode M π hπ m a ha he ρ hρ hex hp hatlas hbc side ≫
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))) r := by
  simp only [firstStrictOuterSpecialMap, Category.assoc, firstMiddleSpecialFibreIso_hom_snd]
  rw [firstStrictOuterToNode, firstOuterSpecialToNode_snd]
  rfl

@[reassoc] lemma firstStrictOuter_global :
    firstStrictOuterSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc side ≫
      pullback.fst (g ≫ structureMap W) r ≫ g =
        firstStrictOuterToCommon M π hπ m a ha he ρ hρ hex hp hatlas hbc side ≫ (C₀).toGlobal := by
  simp only [firstStrictOuterSpecialMap, Category.assoc, firstMiddleSpecialFibreIso_hom_fst_assoc]
  rw [← originalAfterFirst_triangle M π hπ m a ha he ρ hρ hex hp hatlas hbc]
  exact firstOuterSpecial_global hex hp hatlas hbc m S₀ side (structureMap W)

@[reassoc] lemma firstStrictOuter_node :
    firstStrictOuterToCommon M π hπ m a ha he ρ hρ hex hp hatlas hbc side ≫ (C₀).toNode =
      firstStrictOuterToNode M π hπ m a ha he ρ hρ hex hp hatlas hbc side ≫
        Resolution.firstOuterOriginal (π := π) m side :=
  firstOuterSpecial_original_node hex hp hatlas hbc m S₀ side (structureMap W)
    (firstMiddle_initial_base M π hπ m a ha he ρ hρ)

/-- The requested actual full scheme comparison, simultaneously for the left
and right charts and uniformly including thickness two. -/
def firstStrictOuterPullbackIso :
    pullback i (firstStrictOuterSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc side) ≅
      pullback (firstStrictOuterToNode M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
        (Resolution.outerEndBranch hπ) := by
  let := firstStrictOuterSpecialMap_etale M π hπ m a ha he ρ hρ hex hp hatlas hbc side
  let := firstStrictOuterToNode_etale M π hπ m a ha he ρ hρ hex hp hatlas hbc side
  let : IsIntegral (Scheme.Opens.toScheme (X := F) V) :=
    strictPunctured_integral M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp hatlas
      hbc
  let : IsLocallyNoetherian F :=
    finalSpecialFibre_noetherian M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp
      hatlas hbc
  let : QuasiCompact (Scheme.Opens.ι (X := F) V) := by infer_instance
  exact Chart.Step.outerStrictPullbackIso C₀ (Scheme.Opens.ι (X := F) V)
    (pullback.fst (g ≫ structureMap W) r ≫ g)
    (firstStrictOuterSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
    (firstStrictOuterToCommon M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
    (firstStrictOuterToNode M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
    (Resolution.firstOuterOriginal (π := π) m side)
    (strictPunctured_original_range_eq M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex
      hp hatlas hbc)
    (Resolution.firstOuterOriginal_puncture_range hπ m side)
    (firstStrictOuter_global M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
    (firstStrictOuter_node M π hπ m a ha he ρ hρ hex hp hatlas hbc side)

@[reassoc] lemma firstStrictOuterPullbackIso_hom_fst :
    (firstStrictOuterPullbackIso M π hπ m a ha he ρ hρ hex hp hatlas hbc side).hom ≫
      pullback.fst (firstStrictOuterToNode M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
        (Resolution.outerEndBranch hπ) =
      pullback.snd i (firstStrictOuterSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc side) := by
  let := firstStrictOuterSpecialMap_etale M π hπ m a ha he ρ hρ hex hp hatlas hbc side
  let := firstStrictOuterToNode_etale M π hπ m a ha he ρ hρ hex hp hatlas hbc side
  let : IsIntegral (Scheme.Opens.toScheme (X := F) V) :=
    strictPunctured_integral M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp hatlas
      hbc
  let : IsLocallyNoetherian F :=
    finalSpecialFibre_noetherian M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp
      hatlas hbc
  let : QuasiCompact (Scheme.Opens.ι (X := F) V) := by infer_instance
  exact Chart.Step.outerStrictPullbackIso_hom_fst C₀ (Scheme.Opens.ι (X := F) V)
    (pullback.fst (g ≫ structureMap W) r ≫ g)
    (firstStrictOuterSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
    (firstStrictOuterToCommon M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
    (firstStrictOuterToNode M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
    (Resolution.firstOuterOriginal (π := π) m side)
    (strictPunctured_original_range_eq M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ
      hex hp hatlas hbc)
    (Resolution.firstOuterOriginal_puncture_range hπ m side)
    (firstStrictOuter_global M π hπ m a ha he ρ hρ hex hp hatlas hbc side)
    (firstStrictOuter_node M π hπ m a ha he ρ hρ hex hp hatlas hbc side)

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassRetainedOuterStrict

section WeierstrassFirstSpecialCover

/-! The actual punctured open, full retained first left/right residue charts,
and entire first middle residue chart cover the SAME final special fibre. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (m : ℕ)
  (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 2)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "S₀" => initialState M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ
local notation "BG" => State.blowup S₀ hex
local notation "f" => runAfterFirstMap hex hp hatlas hbc m S₀
local notation "g" => modification M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex hp
  hatlas hbc
local notation "r" => Resolution.residueBase (R := R)
local notation "F" => finalSpecialFibre M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ hex
  hp hatlas hbc
local notation "V" => strictPuncturedOpen M π hπ (m + 2) (Nat.zero_lt_succ (m + 1)) a ha he ρ hρ
  hex hp hatlas hbc
local notation "e" => firstMiddleSpecialFibreIso M π hπ m a ha he ρ hρ hex hp hatlas hbc

@[reassoc] lemma firstSpecialFibreIso_inv_original :
    (e).inv ≫ pullback.fst (f ≫ (BG).map ≫ structureMap W) r ≫ f ≫ (BG).map =
      pullback.fst (g ≫ structureMap W) r ≫ g := by
  have H : (e).hom ≫ pullback.fst (g ≫ structureMap W) r ≫ g =
      pullback.fst (f ≫ (BG).map ≫ structureMap W) r ≫ f ≫ (BG).map := by
    rw [firstMiddleSpecialFibreIso_hom_fst_assoc, originalAfterFirst_triangle]
  rw [← H, Iso.inv_hom_id_assoc]

/-- Actual chart-image coverage; the original common chart is only lifted
above the original residue point, using its full centre square. -/
lemma strictPunctured_firstSpecialCharts_cover (z : F) :
    z ∈ Set.range (Scheme.Opens.ι (X := F) V) ∨
      z ∈ Set.range (firstStrictOuterSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc false) ∨
        z ∈ Set.range (firstStrictOuterSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc true) ∨
          z ∈ Set.range (firstMiddleSpecialMap M π hπ m a ha he ρ hρ hex hp hatlas hbc) := by
  by_cases hz : (pullback.fst (g ≫ structureMap W) r ≫ g) z ∈ Set.range (residueNodeMap W x y he)
  · right
    have hz' : (pullback.fst (f ≫ (BG).map ≫ structureMap W) r ≫ f ≫ (BG).map) ((e).inv z) ∈
        Set.range (S₀).chart.globalPoint := by
      change ((e).inv ≫ pullback.fst (f ≫ (BG).map ≫ structureMap W) r ≫ f ≫ (BG).map) z ∈ _
      rw [firstSpecialFibreIso_inv_original]
      exact hz
    rcases firstSpecialCharts_cover hex hp hatlas hbc m S₀ (structureMap W) ((e).inv z) hz'
      with hl | hm | hr
    · left
      obtain ⟨v, hv⟩ := hl
      refine ⟨v, ?_⟩
      change (e).hom (firstOuterSpecialMap hex hp hatlas hbc m S₀ false (structureMap W) v) = z
      rw [hv]
      exact (congrArg (fun q => q z) (e).inv_hom_id)
    · right; right
      obtain ⟨v, hv⟩ := hm
      refine ⟨v, ?_⟩
      change (e).hom (Chart.Step.laterMiddleSpecialMap (S₀).chart
        (OneStepBlowup.ofFamilies π m hex hp hatlas) (BG) ((S₀).commonBlowup hex) (structureMap W)
          f v) = z
      rw [hv]
      exact (congrArg (fun q => q z) (e).inv_hom_id)
    · right; left
      obtain ⟨v, hv⟩ := hr
      refine ⟨v, ?_⟩
      change (e).hom (firstOuterSpecialMap hex hp hatlas hbc m S₀ true (structureMap W) v) = z
      rw [hv]
      exact (congrArg (fun q => q z) (e).inv_hom_id)
  · left
    rw [strictPunctured_original_range_eq]
    exact hz

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassFirstSpecialCover
