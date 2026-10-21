/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.WeierstrassStrictTransformCover
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.NodeChainIntersections

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.NativeStrictIntersections`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`fac02b501b47bacc71f37f16530448525acab94fcb52ebfe8953089e2849de5f`.
Only source260–386: two actual Run first-common/blowup squares and their original Weierstrass
  first-common specialization. The earlier model/cycle/two-point endpoint record assembly is
  excluded.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode

section RunFirstBlowupSquares

/-! Cartesian first-blowup comparison squares for the entire actual Run.
These retain exactly the already defined maps on both the global and node sides. -/
noncomputable section
set_option autoImplicit false
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
  {ha : BlowupAffineAtlas.{u}} {hbc : BlowupFlatBaseChange.{u}}

lemma firstCommonToBlowup_global_square : ∀ (m : ℕ)
    (S : State X q₀ π hπ (m + 2) (by omega)) (T : Run hex hp ha hbc S),
    IsPullback (firstCommonToBlowup T (by omega)) T.fullCommonToGlobal
      (Chart.Step.toGlobal S.chart (S.blowup hex) (S.commonBlowup hex))
      (T.afterFirstMap (by omega))
  | 0, S, T => by
    cases T with
    | two S =>
      let : IsIso (firstCommonToBlowup (Run.two S : Run hex hp ha hbc S) (by omega)) := by
        change IsIso (twoFullCommonIso hex hp ha hbc S).inv
        infer_instance
      let : IsIso (afterFirstMap (Run.two S : Run hex hp ha hbc S) (by omega)) := by
        change IsIso (𝟙 _)
        infer_instance
      exact IsPullback.of_horiz_isIso ⟨firstCommonToBlowup_global 0 S (Run.two S)⟩
  | m + 1, S, T => by
    cases T with
    | next m S tail =>
      apply (Step.retained_square S hex hp ha hbc tail).flip.of_iso
        (Step.retainedFullCommonIso S hex hp ha hbc tail)
        (Iso.refl _) (Iso.refl _) (Iso.refl _)
      · simp [firstCommonToBlowup]
      · simp
      · simp
      · simp [afterFirstMap]

lemma firstCommonToBlowup_node_square : ∀ (m : ℕ)
    (S : State X q₀ π hπ (m + 2) (by omega)) (T : Run hex hp ha hbc S),
    IsPullback (fullNodeComparison T) (firstCommonToBlowup T (by omega))
      (Resolution.stepToBlowup (OneStepBlowup.ofFamilies π m hex hp ha)
        hπ (Resolution.resolve π hπ hex hp ha m))
      (Chart.Step.toNode S.chart (OneStepBlowup.ofFamilies π m hex hp ha) (S.commonBlowup hex))
  | 0, S, T => by
    cases T with
    | two S =>
      let : IsIso (firstCommonToBlowup (Run.two S : Run hex hp ha hbc S) (by omega)) := by
        change IsIso (twoFullCommonIso hex hp ha hbc S).inv
        infer_instance
      let : IsIso (Resolution.stepToBlowup (OneStepBlowup.ofFamilies π 0 hex hp ha)
          hπ (Resolution.resolve π hπ hex hp ha 0)) := by
        change IsIso (Resolution.resolveTwoBlowupIso π hπ hex hp ha).hom
        infer_instance
      exact IsPullback.of_vert_isIso ⟨(firstCommonToBlowup_node 0 S (Run.two S)).symm⟩
  | m + 1, S, T => by
    cases T with
    | next m S tail =>
      apply (Step.Comparison.gluedComparison_square S hex hp ha hbc tail
        (Resolution.resolve π hπ hex hp ha (m + 1)) (fullNodeComparison tail)
        (fullNodeComparison_square tail)).of_iso
        (Step.retainedFullCommonIso S hex hp ha hbc tail)
        (Iso.refl _) (Iso.refl _) (Iso.refl _)
      · simp [fullNodeComparison, fullNodeComparisonData, Step.Comparison.nextNodeComparison]
      · simp [firstCommonToBlowup]
      · simp
      · simp

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run

end -- noncomputable section
end RunFirstBlowupSquares


section FirstOuterCommonSquares

/-! Exact first-common global square for the same exceptional P1.
The accepted originalP1FirstCommon_node triangle supplies the node projection. -/
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
local notation "T" => originalRun M π hπ (m + 2) (Nat.succ_pos (m + 1))
  a ha he ρ hρ hex hp hatlas hbc
local notation "BG" => State.blowup S hex
local notation "BC" => State.commonBlowup S hex
local notation "D" => OneStepBlowup.ofFamilies π m hex hp hatlas
local notation "A" => runAfterFirstMap hex hp hatlas hbc m S
local notation "g" => modification M π hπ (m + 2) (Nat.succ_pos (m + 1))
  a ha he ρ hρ hex hp hatlas hbc
local notation "r" => Resolution.residueBase (R := R)
local notation "E" => Resolution.resolve π hπ hex hp hatlas (m + 2)
local notation "P" => originalExceptionalP1 M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc
local notation "N" => Resolution.interiorComponent π hπ hex hp hatlas (m + 1)

lemma originalP1FirstCommon_global_square (j : Fin (m + 1)) :
    IsPullback (originalP1FirstCommon M π hπ m a ha he ρ hρ hex hp hatlas hbc j)
      (𝟙 _) (Chart.Step.toGlobal C BG BC)
      (P j ≫ pullback.fst (g ≫ structureMap W) r ≫ A) := by
  have H := (Run.commonExceptionalMap_global_square T
    (Resolution.exceptionalP1 π hπ hex hp hatlas (m + 1) j)).paste_horiz
      (Run.firstCommonToBlowup_global_square m S T)
  change IsPullback (originalP1FirstCommon M π hπ m a ha he ρ hρ hex hp hatlas hbc j)
    (𝟙 _) (Chart.Step.toGlobal C BG BC)
    (Run.globalExceptionalMap T (Resolution.exceptionalP1 π hπ hex hp hatlas (m + 1) j) ≫ A) at H
  have Hmap : Run.globalExceptionalMap T
      (Resolution.exceptionalP1 π hπ hex hp hatlas (m + 1) j) ≫ A =
      P j ≫ pullback.fst (g ≫ structureMap W) r ≫ A := by
    calc
      _ = originalP1FirstCommon M π hπ m a ha he ρ hρ hex hp hatlas hbc j ≫
          Chart.Step.toGlobal C BG BC := by simpa only [Category.id_comp] using H.w.symm
      _ = _ := originalP1FirstCommon_global M π hπ m a ha he ρ hρ hex hp hatlas hbc j
  rw [Hmap] at H
  exact H

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end FirstOuterCommonSquares
