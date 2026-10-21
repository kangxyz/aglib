/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.PointedEtale.Charts

/-!
Native extraction from the R5 local-model source
`PointedResolution.PointedEtale.Runs`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`ff1e06845b3b68ef4240398b750d3a1cd8106afc24c3284414e86d83520a9580`.
Actual arbitrary-scheme pointed node charts/states and constructed transitions; all four blowup
  families remain explicit. Runs omits source230–318 Weierstrass initial assembly.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

/-!
# Finite pointed modification runs, exponent descent and the invariant from the original
  Weierstrass node.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode
universe u

section PointedModificationStep


/-! Properness, local Noetherianity and the triangle to a fixed original point
are preserved constructively by the actual next global blowup. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.State
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π} {m : ℕ}
variable (S : State X q₀ π hπ (m + 2) (Nat.succ_pos (m + 1)))
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})

/-- The blowup of the current global marked-point centre chosen from the supplied existence family.
-/
def blowup : BlowupDatum S.chart.globalPoint.ker := S.chart.globalBlowup hex

/-- The blowup of the current common marked-point centre chosen from the supplied existence family.
-/
def commonBlowup : BlowupDatum S.chart.center := S.chart.commonBlowup hex

include hp in
lemma blowup_proper : IsProper (blowup S hex).map := S.chart.globalBlowup_proper hex hp

include hp in
lemma blowup_noetherian : IsLocallyNoetherian (blowup S hex).Y := by
  let := blowup_proper S hex hp
  exact LocallyOfFiniteType.isLocallyNoetherian (blowup S hex).map

/-- The same global source after one actual point blowup, with exponent m. -/
def step (hm : 0 < m) : State X q₀ π hπ m hm := by
  let BG := blowup S hex
  let BC := commonBlowup S hex
  let D := OneStepBlowup.ofFamilies π m hex hp hatlas
  let : IsProper BG.map := blowup_proper S hex hp
  exact {
    Y := BG.Y
    map := BG.map ≫ S.map
    proper := inferInstance
    noetherian := blowup_noetherian S hex hp
    chart := Chart.Step.nextChart S.chart D BG BC hm hbc
    point_triangle := by rw [← Category.assoc, Chart.Step.next_global_blowdown, S.point_triangle] }

@[simp] lemma step_map (hm : 0 < m) :
    (step S hex hp hatlas hbc hm).map = (blowup S hex).map ≫ S.map := rfl

include hbc in
/-- Both actual canonical blowup squares are retained at each transition. -/
lemma step_cartesian :
    IsPullback (Chart.Step.toGlobal S.chart (blowup S hex) (commonBlowup S hex))
      (commonBlowup S hex).map (blowup S hex).map S.chart.toGlobal ∧
    IsPullback (Chart.Step.toNode S.chart (OneStepBlowup.ofFamilies π m hex hp hatlas)
      (commonBlowup S hex)) (commonBlowup S hex).map
      (OneStepBlowup.ofFamilies π m hex hp hatlas).blowup.map S.chart.toNode :=
  ⟨Chart.Step.global_square _ _ _ hbc, Chart.Step.node_square _ _ _ hbc⟩

/-- The middle chart is retained at zero without any selected residue origin. -/
def zeroMiddle (S : State X q₀ π hπ 2 (by decide))
    (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
    (hatlas : BlowupAffineAtlas.{u}) : Scheme.{u} :=
  Chart.Step.middle S.chart (OneStepBlowup.ofFamilies π 0 hex hp hatlas) (commonBlowup S hex)

/-- Map the terminal exponent-zero middle chart into the global blowup of an exponent-two state. -/
def zeroMiddleToGlobal (S : State X q₀ π hπ 2 (by decide))
    (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
    (hatlas : BlowupAffineAtlas.{u}) :
    zeroMiddle S hex hp hatlas ⟶ (blowup S hex).Y :=
  Chart.Step.middleToGlobal S.chart (OneStepBlowup.ofFamilies π 0 hex hp hatlas)
    (blowup S hex) (commonBlowup S hex)

/-- Project the terminal middle chart of an exponent-two state to the exponent-zero node. -/
def zeroMiddleToNode (S : State X q₀ π hπ 2 (by decide))
    (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
    (hatlas : BlowupAffineAtlas.{u}) :
    zeroMiddle S hex hp hatlas ⟶ Spec (.of (node π 0)) :=
  Chart.Step.middleToNode S.chart (OneStepBlowup.ofFamilies π 0 hex hp hatlas) (commonBlowup S hex)

lemma zeroMiddleToGlobal_etale (S : State X q₀ π hπ 2 (by decide))
    (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
    (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u}) :
    Etale (zeroMiddleToGlobal S hex hp hatlas) :=
  Chart.Step.middleToGlobal_etale _ _ _ _ hbc
lemma zeroMiddleToNode_etale (S : State X q₀ π hπ 2 (by decide))
    (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
    (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u}) :
    Etale (zeroMiddleToNode S hex hp hatlas) :=
  Chart.Step.middleToNode_etale _ _ _ hbc

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.State

end
end PointedModificationStep

section FinitePointedBlowupRun


/-! Finite iteration of the constructive pointed invariant. The trace retains
all actual states and both canonical cartesian blowup squares. It stops at
one without a blowup, and at two after the UV=1 middle-chart step. This is a
proper blowup sequence with a terminal regular etale common chart, not yet a
global regularity theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π}

/-- A finite pointed blowup run reducing the exponent by two, terminating at exponent one or after
the exponent-two blowup. -/
inductive Run (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
    (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u}) :
    {n : ℕ} → {hn : 0 < n} → State X q₀ π hπ n hn → Type (u + 1)
  | one (S : State X q₀ π hπ 1 (by decide)) : Run hex hp hatlas hbc S
  | two (S : State X q₀ π hπ 2 (by decide)) : Run hex hp hatlas hbc S
  | next (m : ℕ) (S : State X q₀ π hπ (m + 3) (by omega))
      (tail : Run hex hp hatlas hbc (S.step hex hp hatlas hbc (by omega : 0 < m + 1))) :
      Run hex hp hatlas hbc S

variable (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})

/-- The exponent decreases by two, so this is actual finite recursion. -/
def run : (n : ℕ) → (hn : 0 < n) → (S : State X q₀ π hπ n hn) → Run hex hp hatlas hbc S
  | 0, hn, _ => False.elim (by omega)
  | 1, _, S => .one S
  | 2, _, S => .two S
  | m + 3, _, S => .next m S (run (m + 1) (by omega) (S.step hex hp hatlas hbc (by omega)))
termination_by n => n

namespace Run
variable {hex hp hatlas hbc}

/-- The final global source scheme obtained by the finite pointed blowup run. -/
def source : {n : ℕ} → {hn : 0 < n} → {S : State X q₀ π hπ n hn} → Run hex hp hatlas hbc S →
  Scheme.{u}
  | _, _, _, .one S => S.Y
  | _, _, _, .two S => (S.blowup hex).Y
  | _, _, _, .next _ _ tail => source tail

/-- The composite modification map from the final run source to the starting state source. -/
def map : {n : ℕ} → {hn : 0 < n} → {S : State X q₀ π hπ n hn} →
    (T : Run hex hp hatlas hbc S) → source T ⟶ S.Y
  | _, _, _, .one S => 𝟙 S.Y
  | _, _, _, .two S => (S.blowup hex).map
  | _, _, _, .next _ S tail => map tail ≫ (S.blowup hex).map

instance proper : {n : ℕ} → {hn : 0 < n} → {S : State X q₀ π hπ n hn} →
    (T : Run hex hp hatlas hbc S) → IsProper (map T)
  | _, _, _, .one S => by
      change IsProper (𝟙 S.Y)
      exact MorphismProperty.id_mem @IsProper S.Y
  | _, _, _, .two S => S.blowup_proper hex hp
  | _, _, _, .next _ S tail => by
      let := proper tail
      let := S.blowup_proper hex hp
      dsimp [map]; infer_instance

instance noetherian : {n : ℕ} → {hn : 0 < n} → {S : State X q₀ π hπ n hn} →
    (T : Run hex hp hatlas hbc S) → IsLocallyNoetherian (source T)
  | _, _, _, .one S => S.noetherian
  | _, _, _, .two S => S.blowup_noetherian hex hp
  | _, _, _, .next _ _ tail => noetherian tail

/-- The composite map from the final run source to the fixed original scheme. -/
def toOriginal {n : ℕ} {hn : 0 < n} {S : State X q₀ π hπ n hn}
    (T : Run hex hp hatlas hbc S) : source T ⟶ X := map T ≫ S.map

instance toOriginal_proper {n : ℕ} {hn : 0 < n} {S : State X q₀ π hπ n hn}
    (T : Run hex hp hatlas hbc S) : IsProper (toOriginal T) := by
  dsimp [toOriginal]; infer_instance

/-- The exponent of the terminal common node chart: one or zero according to the terminal case. -/
def finalExponent : {n : ℕ} → {hn : 0 < n} → {S : State X q₀ π hπ n hn} →
    Run hex hp hatlas hbc S → ℕ
  | _, _, _, .one _ => 1
  | _, _, _, .two _ => 0
  | _, _, _, .next _ _ tail => finalExponent tail

lemma finalExponent_le_one : {n : ℕ} → {hn : 0 < n} → {S : State X q₀ π hπ n hn} →
    (T : Run hex hp hatlas hbc S) → finalExponent T ≤ 1
  | _, _, _, .one _ => by change 1 ≤ 1; omega
  | _, _, _, .two _ => by change 0 ≤ 1; omega
  | _, _, _, .next _ _ tail => finalExponent_le_one tail

/-- The terminal common neighbourhood retained by the run, using the full middle chart at exponent
zero. -/
def common : {n : ℕ} → {hn : 0 < n} → {S : State X q₀ π hπ n hn} →
    Run hex hp hatlas hbc S → Scheme.{u}
  | _, _, _, .one S => S.chart.C
  | _, _, _, .two S => State.zeroMiddle S hex hp hatlas
  | _, _, _, .next _ _ tail => common tail

/-- The etale map from the terminal common neighbourhood to the final global source. -/
def toGlobal : {n : ℕ} → {hn : 0 < n} → {S : State X q₀ π hπ n hn} →
    (T : Run hex hp hatlas hbc S) → common T ⟶ source T
  | _, _, _, .one S => S.chart.toGlobal
  | _, _, _, .two S => State.zeroMiddleToGlobal S hex hp hatlas
  | _, _, _, .next _ _ tail => toGlobal tail

/-- The etale map from the terminal common neighbourhood to the node with the final exponent. -/
def toNode : {n : ℕ} → {hn : 0 < n} → {S : State X q₀ π hπ n hn} →
    (T : Run hex hp hatlas hbc S) → common T ⟶ Spec (.of (node π (finalExponent T)))
  | _, _, _, .one S => S.chart.toNode
  | _, _, _, .two S => State.zeroMiddleToNode S hex hp hatlas
  | _, _, _, .next _ _ tail => toNode tail

instance toGlobal_etale : {n : ℕ} → {hn : 0 < n} → {S : State X q₀ π hπ n hn} →
    (T : Run hex hp hatlas hbc S) → Etale (toGlobal T)
  | _, _, _, .one S => S.chart.global_etale
  | _, _, _, .two S => State.zeroMiddleToGlobal_etale S hex hp hatlas hbc
  | _, _, _, .next _ _ tail => toGlobal_etale tail

instance toNode_etale : {n : ℕ} → {hn : 0 < n} → {S : State X q₀ π hπ n hn} →
    (T : Run hex hp hatlas hbc S) → Etale (toNode T)
  | _, _, _, .one S => S.chart.node_etale
  | _, _, _, .two S => State.zeroMiddleToNode_etale S hex hp hatlas hbc
  | _, _, _, .next _ _ tail => toNode_etale tail

end Run
end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end
end FinitePointedBlowupRun
