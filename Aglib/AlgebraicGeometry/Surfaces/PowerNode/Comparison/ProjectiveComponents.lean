/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.FiberChart
public import Aglib.AlgebraicGeometry.Limits.Range
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.NodeOuterFibres
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Reciprocal

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.ProjectiveComponents`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`4e5f946b7f8fbe1602cc88becc50ec7eaa3c9af9a5770d3c3d3fe57fe34da57c`.
Only literal resolved-node component consumers; general reciprocal P1 comparisons are extracted to
  the existing projective-line family.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre

section NodeResidueTransitions

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme.PowerNode.BlowupOverlaps AlgebraicGeometry.Scheme.Blowup.Coordinates
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {π : R} (hπ : Irreducible π)
local notation "k" => IsLocalRing.ResidueField R

include hπ in
lemma residueLaurent_pi_zero : algebraMap R (Reciprocal.Laurent k) π = 0 := by
  rw [IsScalarTower.algebraMap_apply R k (Reciprocal.Laurent k), residue_uniformizer hπ, map_zero]

/-- On the punctured exceptional branch, its coordinate is the reciprocal
of the old strict-transform coordinate. -/
def overlapResidueBase : PlaneNode.Ring π →ₐ[R] Reciprocal.Laurent k :=
  PlaneNode.lift π 0 (Reciprocal.invT k) (by rw [zero_mul, residueLaurent_pi_zero hπ])

/-- Extends the residue branch map to the left overlap by sending the inverted `V` coordinate to
an invertible Laurent coordinate. -/
def overlapResidueHom : leftOverlap π →ₐ[R] Reciprocal.Laurent k :=
  IsLocalization.Away.liftAlgHom (PlaneNode.V π) (f := overlapResidueBase hπ) (by
    simp only [overlapResidueBase, PlaneNode.lift_V]
    exact IsUnit.of_mul_eq_one (Reciprocal.t k) (Reciprocal.invT_mul_t k))

@[simp] lemma overlapResidueHom_base (x : PlaneNode.Ring π) :
    overlapResidueHom hπ (algebraMap (PlaneNode.Ring π) _ x) = overlapResidueBase hπ x := by
  simp [overlapResidueHom]

@[simp] lemma overlapResidueHom_inv :
    overlapResidueHom hπ (IsLocalization.Away.invSelf (S := leftOverlap π) (PlaneNode.V π)) =
      Reciprocal.t k := by
  apply Localization.Away.map_invSelf_of_mul
  simp [overlapResidueBase]

lemma residueLeftHom_overlap (m : ℕ) :
    (overlapResidueHom hπ).comp (middleLeftOverlapBase π (m + 1)) =
      ((IsScalarTower.toAlgHom k k[X] (Reciprocal.Laurent k)).restrictScalars R).comp
        (residueLeftHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)) := by
  apply PlaneNode.hom_ext
  · simp [middleLeftOverlapBase, residueLeftHom, Reciprocal.t]
  · simp only [AlgHom.comp_apply, middleLeftOverlapBase, PlaneNode.lift_V, map_mul, AlgHom.commutes,
      residueLeftHom, map_zero]
    rw [map_pow, residueLaurent_pi_zero hπ, zero_pow (Nat.succ_ne_zero m), zero_mul]

lemma residueRightHom_overlap (m : ℕ) :
    (overlapResidueHom hπ).comp (middleRightOverlapBase π (m + 1)) =
      ((IsScalarTower.toAlgHom k k[X] (Reciprocal.Laurent k)).restrictScalars R).comp
        (residueRightHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)) := by
  apply PlaneNode.hom_ext
  · simp only [AlgHom.comp_apply, middleRightOverlapBase, nodeSwap_u, middleLeftOverlapBase,
      PlaneNode.lift_V, map_mul, AlgHom.commutes, residueRightHom, PlaneNode.lift_U, map_zero]
    rw [map_pow, residueLaurent_pi_zero hπ, zero_pow (Nat.succ_ne_zero m), zero_mul]
  · simp [middleRightOverlapBase, middleLeftOverlapBase, residueRightHom, Reciprocal.t]

lemma overlapResidueBase_eq : overlapResidueBase hπ =
    ((aeval (Reciprocal.invT k)).restrictScalars R).comp
      (residueRightHom π (residue_uniformizer hπ)) := by
  apply PlaneNode.hom_ext <;> simp [overlapResidueBase, residueRightHom]

/-- Explicit parameter-level compatibility in the same actual blowup. -/
@[reassoc] lemma left_residue_transition (m : ℕ) (B : OneStepBlowup.Data π (m + 1)) :
    Reciprocal.toZeroChart k ≫
      Spec.map (CommRingCat.ofHom
        (residueLeftHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom) ≫
      middleChartMap B.atlas hπ =
    Reciprocal.toInfinityChart k ≫
      Spec.map (CommRingCat.ofHom (residueRightHom π (residue_uniformizer hπ)).toRingHom) ≫
      leftChartMap B.atlas hπ := by
  have h₁ : Spec.map (CommRingCat.ofHom (overlapResidueHom hπ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (middleLeftOverlapBase π (m + 1)).toRingHom) =
      Reciprocal.toZeroChart k ≫ Spec.map (CommRingCat.ofHom
        (residueLeftHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom) := by
    rw [Reciprocal.toZeroChart, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom)) (residueLeftHom_overlap hπ m)
  have h₂ : Spec.map (CommRingCat.ofHom (overlapResidueHom hπ).toRingHom) ≫ awayMap (PlaneNode.V
    π) =
      Reciprocal.toInfinityChart k ≫
        Spec.map (CommRingCat.ofHom (residueRightHom π (residue_uniformizer hπ)).toRingHom) := by
    rw [awayMap, Reciprocal.toInfinityChart, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (overlapResidueHom_base hπ x).trans (DFunLike.congr_fun (overlapResidueBase_eq hπ) x)
  calc
    _ = (Spec.map (CommRingCat.ofHom (overlapResidueHom hπ).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (middleLeftOverlapBase π (m + 1)).toRingHom)) ≫
          middleChartMap B.atlas hπ := by rw [h₁, Category.assoc]
    _ = (Spec.map (CommRingCat.ofHom (overlapResidueHom hπ).toRingHom) ≫ awayMap (PlaneNode.V π)) ≫
          leftChartMap B.atlas hπ := by
        simpa only [← Category.assoc] using
          (congrArg (Spec.map (CommRingCat.ofHom (overlapResidueHom hπ).toRingHom) ≫ ·)
            (leftMiddle_explicit_triangle hπ B))
    _ = _ := by rw [h₂, Category.assoc]

@[reassoc] lemma right_residue_transition (m : ℕ) (B : OneStepBlowup.Data π (m + 1)) :
    Reciprocal.toZeroChart k ≫
      Spec.map (CommRingCat.ofHom
        (residueRightHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom) ≫
      middleChartMap B.atlas hπ =
    Reciprocal.toInfinityChart k ≫
      Spec.map (CommRingCat.ofHom (residueRightHom π (residue_uniformizer hπ)).toRingHom) ≫
      rightChartMap B.atlas hπ := by
  have h₁ : Spec.map (CommRingCat.ofHom (overlapResidueHom hπ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (middleRightOverlapBase π (m + 1)).toRingHom) =
      Reciprocal.toZeroChart k ≫ Spec.map (CommRingCat.ofHom
        (residueRightHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom) := by
    rw [Reciprocal.toZeroChart, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom)) (residueRightHom_overlap hπ
      m)
  have h₂ : Spec.map (CommRingCat.ofHom (overlapResidueHom hπ).toRingHom) ≫ awayMap (PlaneNode.V
    π) =
      Reciprocal.toInfinityChart k ≫
        Spec.map (CommRingCat.ofHom (residueRightHom π (residue_uniformizer hπ)).toRingHom) := by
    rw [awayMap, Reciprocal.toInfinityChart, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (overlapResidueHom_base hπ x).trans (DFunLike.congr_fun (overlapResidueBase_eq hπ) x)
  calc
    _ = (Spec.map (CommRingCat.ofHom (overlapResidueHom hπ).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (middleRightOverlapBase π (m + 1)).toRingHom)) ≫
          middleChartMap B.atlas hπ := by rw [h₁, Category.assoc]
    _ = (Spec.map (CommRingCat.ofHom (overlapResidueHom hπ).toRingHom) ≫ awayMap (PlaneNode.V π)) ≫
          rightChartMap B.atlas hπ := by
        simpa only [← Category.assoc] using
          (congrArg (Spec.map (CommRingCat.ofHom (overlapResidueHom hπ).toRingHom) ≫ ·)
            (rightMiddle_explicit_triangle hπ B))
    _ = _ := by rw [h₂, Category.assoc]

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeResidueTransitions


section NodeStepChartCompatibility

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.OpenPushout.Modification.OfRestriction
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {π : R} {m : ℕ} (B : OneStepBlowup.Data π m) (hπ : Irreducible π)
  (E : Data π m)

@[reassoc] lemma stepModifiedChart_toBlowup :
    stepModifiedChart B hπ E ≫ stepToBlowup B hπ E = E.map ≫ middleChartMap B.atlas hπ :=
  modifiedChart_triangle ..
@[reassoc] lemma stepUnchangedChart_toBlowup :
    stepUnchangedChart B hπ E ≫ stepToBlowup B hπ E = (outerOpen B hπ).ι :=
  unchangedChart_triangle ..
@[reassoc] lemma stepLeftChart_toBlowup :
    stepLeftChart B hπ E ≫ stepToBlowup B hπ E = leftChartMap B.atlas hπ := by
  rw [stepLeftChart, Category.assoc, stepUnchangedChart_toBlowup, outerLeftChart_triangle]
@[reassoc] lemma stepRightChart_toBlowup :
    stepRightChart B hπ E ≫ stepToBlowup B hπ E = rightChartMap B.atlas hπ := by
  rw [stepRightChart, Category.assoc, stepUnchangedChart_toBlowup, outerRightChart_triangle]

/-- The identity pullback on the unchanged open gives uniqueness of lifts
there. This is used to keep explicit overlap formulas in the actual source. -/
lemma step_lift_to_unchanged {T : Scheme.{u}}
    (u : T ⟶ (outerOpen B hπ).toScheme) (v : T ⟶ (step B hπ E).Y)
    (h : u ≫ (outerOpen B hπ).ι = v ≫ stepToBlowup B hπ E) :
    u ≫ stepUnchangedChart B hπ E = v := by
  let H := stepUnchangedChart_isPullback B hπ E
  have hu : H.lift u v h = u := by simpa using H.lift_fst u v h
  simpa only [hu] using H.lift_snd u v h

lemma step_left_chart_agree {T : Scheme.{u}} (f : T ⟶ E.Y)
    (g : T ⟶ Spec (.of (PlaneNode.Ring π)))
    (h : f ≫ E.map ≫ middleChartMap B.atlas hπ = g ≫ leftChartMap B.atlas hπ) :
    f ≫ stepModifiedChart B hπ E = g ≫ stepLeftChart B hπ E := by
  symm
  rw [stepLeftChart, ← Category.assoc]
  apply step_lift_to_unchanged
  rw [Category.assoc, outerLeftChart_triangle, Category.assoc, stepModifiedChart_toBlowup]
  exact h.symm

lemma step_right_chart_agree {T : Scheme.{u}} (f : T ⟶ E.Y)
    (g : T ⟶ Spec (.of (PlaneNode.Ring π)))
    (h : f ≫ E.map ≫ middleChartMap B.atlas hπ = g ≫ rightChartMap B.atlas hπ) :
    f ≫ stepModifiedChart B hπ E = g ≫ stepRightChart B hπ E := by
  symm
  rw [stepRightChart, ← Category.assoc]
  apply step_lift_to_unchanged
  rw [Category.assoc, outerRightChart_triangle, Category.assoc, stepModifiedChart_toBlowup]
  exact h.symm

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeStepChartCompatibility


section NodeFibreComponentGluing

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
variable {π : R} (hπ : Irreducible π) (m : ℕ)
  (B : OneStepBlowup.Data π (m + 1)) (E : Data π (m + 1))
local notation "k" => IsLocalRing.ResidueField R

/-- Compactify an actual old left A1 end by the new exceptional A1 chart.
The compatibility is proved in the same recursively constructed source. -/
lemma left_end_reciprocal (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueLeftHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) :
    Reciprocal.toZeroChart k ≫ e ≫ middleFibreChart B hπ E =
      Reciprocal.toInfinityChart k ≫ outerExceptionalBranch hπ ≫ leftFibreChart B hπ E := by
  apply pullback.hom_ext
  · simp only [Category.assoc, middleFibreChart_source_triangle, leftFibreChart_source_triangle,
      outerExceptionalBranch_fst_assoc]
    have h := step_left_chart_agree B hπ E
      (Reciprocal.toZeroChart k ≫ e ≫ pullback.fst (E.map ≫ base) residueBase)
      (Reciprocal.toInfinityChart k ≫
        Spec.map (CommRingCat.ofHom (residueRightHom π (residue_uniformizer hπ)).toRingHom)) (by
        simpa only [Category.assoc, reassoc_of% he] using left_residue_transition hπ m B)
    simpa only [Category.assoc] using h
  · simp only [Category.assoc, middleFibreChart_base_triangle, leftFibreChart_base_triangle,
      outerExceptionalBranch_snd, hb]
    exact (Reciprocal.toZeroChart_over k).trans (Reciprocal.toInfinityChart_over k).symm

lemma right_end_reciprocal (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueRightHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) :
    Reciprocal.toZeroChart k ≫ e ≫ middleFibreChart B hπ E =
      Reciprocal.toInfinityChart k ≫ outerExceptionalBranch hπ ≫ rightFibreChart B hπ E := by
  apply pullback.hom_ext
  · simp only [Category.assoc, middleFibreChart_source_triangle, rightFibreChart_source_triangle,
      outerExceptionalBranch_fst_assoc]
    have h := step_right_chart_agree B hπ E
      (Reciprocal.toZeroChart k ≫ e ≫ pullback.fst (E.map ≫ base) residueBase)
      (Reciprocal.toInfinityChart k ≫
        Spec.map (CommRingCat.ofHom (residueRightHom π (residue_uniformizer hπ)).toRingHom)) (by
        simpa only [Category.assoc, reassoc_of% he] using right_residue_transition hπ m B)
    simpa only [Category.assoc] using h
  · simp only [Category.assoc, middleFibreChart_base_triangle, rightFibreChart_base_triangle,
      outerExceptionalBranch_snd, hb]
    exact (Reciprocal.toZeroChart_over k).trans (Reciprocal.toInfinityChart_over k).symm

section Left

/-- Glues the given middle affine branch and the left outer exceptional branch by their reciprocal
overlap maps. -/
def stepLeftCompactification (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueLeftHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) : projectiveP1 k
      ⟶ sourceSpecialFibre (step B hπ E) :=
  Reciprocal.descend k (e ≫ middleFibreChart B hπ E)
    (outerExceptionalBranch hπ ≫ leftFibreChart B hπ E)
    (left_end_reciprocal hπ m B E e he hb)

@[reassoc] lemma stepLeftCompactification_zero_chart (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueLeftHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) :
    chart k 0 ≫ stepLeftCompactification hπ m B E e he hb = e ≫ middleFibreChart B hπ E :=
  Reciprocal.chart_zero_descend ..
@[reassoc] lemma stepLeftCompactification_infinity_chart (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueLeftHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) :
    chart k 1 ≫ stepLeftCompactification hπ m B E e he hb =
      outerExceptionalBranch hπ ≫ leftFibreChart B hπ E := Reciprocal.chart_infinity_descend ..

@[reassoc] lemma stepLeftCompactification_base (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueLeftHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) :
    stepLeftCompactification hπ m B E e he hb ≫
      pullback.snd ((step B hπ E).map ≫ base) residueBase = structureMap k := by
  apply Reciprocal.descend_over
  · simpa only [Category.assoc, middleFibreChart_base_triangle] using hb
  · rw [Category.assoc, leftFibreChart_base_triangle, outerExceptionalBranch_snd]
    rfl

@[reassoc] lemma stepLeftCompactification_old_endpoint (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueLeftHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) :
    Reciprocal.zeroSection k ≫ stepLeftCompactification hπ m B E e he hb =
      Cross.endpoint k ≫ e ≫ middleFibreChart B hπ E := Reciprocal.zeroSection_descend ..
@[reassoc] lemma stepLeftCompactification_new_endpoint (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueLeftHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) :
    Reciprocal.infinitySection k ≫ stepLeftCompactification hπ m B E e he hb =
      outerNode hπ ≫ leftFibreChart B hπ E := by
  rw [stepLeftCompactification, Reciprocal.infinitySection_descend, ← Category.assoc]
  change (Cross.endpoint k ≫ outerExceptionalBranch hπ) ≫ _ = _
  rw [outerExceptionalBranch_endpoint]
end Left

section Right

/-- Glues the given middle affine branch and the right outer exceptional branch by their
reciprocal overlap maps. -/
def stepRightCompactification (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueRightHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) : projectiveP1 k
      ⟶ sourceSpecialFibre (step B hπ E) :=
  Reciprocal.descend k (e ≫ middleFibreChart B hπ E)
    (outerExceptionalBranch hπ ≫ rightFibreChart B hπ E)
    (right_end_reciprocal hπ m B E e he hb)

@[reassoc] lemma stepRightCompactification_zero_chart (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueRightHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) :
    chart k 0 ≫ stepRightCompactification hπ m B E e he hb = e ≫ middleFibreChart B hπ E :=
  Reciprocal.chart_zero_descend ..
@[reassoc] lemma stepRightCompactification_infinity_chart (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueRightHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) :
    chart k 1 ≫ stepRightCompactification hπ m B E e he hb =
      outerExceptionalBranch hπ ≫ rightFibreChart B hπ E := Reciprocal.chart_infinity_descend ..

@[reassoc] lemma stepRightCompactification_base (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueRightHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) :
    stepRightCompactification hπ m B E e he hb ≫
      pullback.snd ((step B hπ E).map ≫ base) residueBase = structureMap k := by
  apply Reciprocal.descend_over
  · simpa only [Category.assoc, middleFibreChart_base_triangle] using hb
  · rw [Category.assoc, rightFibreChart_base_triangle, outerExceptionalBranch_snd]
    rfl

@[reassoc] lemma stepRightCompactification_old_endpoint (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueRightHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) :
    Reciprocal.zeroSection k ≫ stepRightCompactification hπ m B E e he hb =
      Cross.endpoint k ≫ e ≫ middleFibreChart B hπ E := Reciprocal.zeroSection_descend ..
@[reassoc] lemma stepRightCompactification_new_endpoint (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueRightHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) :
    Reciprocal.infinitySection k ≫ stepRightCompactification hπ m B E e he hb =
      outerNode hπ ≫ rightFibreChart B hπ E := by
  rw [stepRightCompactification, Reciprocal.infinitySection_descend, ← Category.assoc]
  change (Cross.endpoint k ≫ outerExceptionalBranch hπ) ≫ _ = _
  rw [outerExceptionalBranch_endpoint]
end Right

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeFibreComponentGluing


section NodeFibreChartIntersections

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme.PowerNode.BlowupOverlaps AlgebraicGeometry.Scheme.Blowup.Coordinates
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution



variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {π : R} {m : ℕ} (B : OneStepBlowup.Data π m) (hπ : Irreducible π) (E : Data π m)

/-- The basic open where the `V` coordinate of the uniformizer node is invertible. -/
def uniformizerVOpen (π : R) : (Spec (.of (PlaneNode.Ring π))).Opens :=
  PrimeSpectrum.basicOpen (PlaneNode.V π)

lemma stepLeftChart_isPullback :
    IsPullback (𝟙 (Spec (.of (PlaneNode.Ring π)))) (stepLeftChart B hπ E)
      (leftChartMap B.atlas hπ) (stepToBlowup B hπ E) := by
  simpa only [outerLeftChart_triangle, stepLeftChart] using
    (IsPullback.of_id_fst (f := outerLeftChart B hπ)).paste_vert
      (stepUnchangedChart_isPullback B hπ E)

lemma stepRightChart_isPullback :
    IsPullback (𝟙 (Spec (.of (PlaneNode.Ring π)))) (stepRightChart B hπ E)
      (rightChartMap B.atlas hπ) (stepToBlowup B hπ E) := by
  simpa only [outerRightChart_triangle, stepRightChart] using
    (IsPullback.of_id_fst (f := outerRightChart B hπ)).paste_vert
      (stepUnchangedChart_isPullback B hπ E)

lemma stepMiddle_preimage_left :
    stepModifiedChart B hπ E ⁻¹' Set.range (stepLeftChart B hπ E) =
      E.map ⁻¹' (uOpen π m : Set (Resolution.X π m)) := by
  rw [range_snd_of_isPullback (stepLeftChart_isPullback B hπ E)]
  change (stepModifiedChart B hπ E ≫ stepToBlowup B hπ E) ⁻¹' _ = _
  rw [stepModifiedChart_toBlowup]
  change E.map ⁻¹' (middleChartMap B.atlas hπ ⁻¹' _) = _
  rw [chart_preimage_of_overlap (awayMap (PlaneNode.U (π ^ m))) (middleChartMap B.atlas hπ)
    (leftChartMap B.atlas hπ)
    (overlap_range B.atlas (generator π m 1) (generator π m 0)
      (dvrMiddleReesEquiv π hπ m).toRingEquiv (dvrLeftReesEquiv π hπ m).toRingEquiv
      (PlaneNode.U (π ^ m)) (middle_left_ratio π hπ m))]
  congr 1
  exact PrimeSpectrum.localization_away_comap_range _ _

lemma stepMiddle_preimage_right :
    stepModifiedChart B hπ E ⁻¹' Set.range (stepRightChart B hπ E) =
      E.map ⁻¹' (vOpen π m : Set (Resolution.X π m)) := by
  rw [range_snd_of_isPullback (stepRightChart_isPullback B hπ E)]
  change (stepModifiedChart B hπ E ≫ stepToBlowup B hπ E) ⁻¹' _ = _
  rw [stepModifiedChart_toBlowup]
  change E.map ⁻¹' (middleChartMap B.atlas hπ ⁻¹' _) = _
  rw [chart_preimage_of_overlap (awayMap (PlaneNode.V (π ^ m))) (middleChartMap B.atlas hπ)
    (rightChartMap B.atlas hπ)
    (overlap_range B.atlas (generator π m 1) (generator π m 2)
      (dvrMiddleReesEquiv π hπ m).toRingEquiv (dvrRightReesEquiv π hπ m).toRingEquiv
      (PlaneNode.V (π ^ m)) (middle_right_ratio π hπ m))]
  congr 1
  exact PrimeSpectrum.localization_away_comap_range _ _

lemma stepLeft_preimage_middle :
    stepLeftChart B hπ E ⁻¹' Set.range (stepModifiedChart B hπ E) =
      (uniformizerVOpen π : Set (Spec (.of (PlaneNode.Ring π)))) := by
  rw [range_snd_of_isPullback (stepModifiedChart_isPullback B hπ E)]
  change (stepLeftChart B hπ E ≫ stepToBlowup B hπ E) ⁻¹' Set.range (middleChartMap B.atlas hπ) = _
  rw [stepLeftChart_toBlowup]
  rw [chart_preimage_of_overlap (awayMap (PlaneNode.V π)) (leftChartMap B.atlas hπ)
    (middleChartMap B.atlas hπ) (left_middle_range hπ B.atlas)]
  exact PrimeSpectrum.localization_away_comap_range _ _

lemma stepRight_preimage_middle :
    stepRightChart B hπ E ⁻¹' Set.range (stepModifiedChart B hπ E) =
      (uniformizerVOpen π : Set (Spec (.of (PlaneNode.Ring π)))) := by
  rw [range_snd_of_isPullback (stepModifiedChart_isPullback B hπ E)]
  change (stepRightChart B hπ E ≫ stepToBlowup B hπ E) ⁻¹' Set.range (middleChartMap B.atlas hπ) = _
  rw [stepRightChart_toBlowup]
  rw [chart_preimage_of_overlap (awayMap (PlaneNode.V π)) (rightChartMap B.atlas hπ)
    (middleChartMap B.atlas hπ) (right_middle_range hπ B.atlas)]
  exact PrimeSpectrum.localization_away_comap_range _ _

lemma leftFibre_preimage_middle :
    leftFibreChart B hπ E ⁻¹' Set.range (middleFibreChart B hπ E) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))) residueBase ⁻¹'
        (uniformizerVOpen π : Set (Spec (.of (PlaneNode.Ring π)))) := by
  dsimp only [leftFibreChart, middleFibreChart, sourceSpecialFibre, outerFibre]
  rw [fibreChart_preimage_range, stepLeft_preimage_middle]

lemma rightFibre_preimage_middle :
    rightFibreChart B hπ E ⁻¹' Set.range (middleFibreChart B hπ E) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))) residueBase ⁻¹'
        (uniformizerVOpen π : Set (Spec (.of (PlaneNode.Ring π)))) := by
  dsimp only [rightFibreChart, middleFibreChart, sourceSpecialFibre, outerFibre]
  rw [fibreChart_preimage_range, stepRight_preimage_middle]

lemma middleFibre_preimage_left :
    middleFibreChart B hπ E ⁻¹' Set.range (leftFibreChart B hπ E) =
      (pullback.fst (E.map ≫ base) residueBase ≫ E.map) ⁻¹'
        (uOpen π m : Set (Resolution.X π m)) := by
  dsimp only [leftFibreChart, middleFibreChart, sourceSpecialFibre, outerFibre]
  rw [fibreChart_preimage_range, stepMiddle_preimage_left]
  rfl

lemma middleFibre_preimage_right :
    middleFibreChart B hπ E ⁻¹' Set.range (rightFibreChart B hπ E) =
      (pullback.fst (E.map ≫ base) residueBase ≫ E.map) ⁻¹'
        (vOpen π m : Set (Resolution.X π m)) := by
  dsimp only [rightFibreChart, middleFibreChart, sourceSpecialFibre, outerFibre]
  rw [fibreChart_preimage_range, stepMiddle_preimage_right]
  rfl

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeFibreChartIntersections


section NodeComponentChartRanges

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
variable {π : R} (hπ : Irreducible π) {m : ℕ}
  (B : OneStepBlowup.Data π m) (E : Data π m)
local notation "k" => IsLocalRing.ResidueField R

lemma leftExceptional_preimage_middle :
    (outerExceptionalBranch hπ ≫ leftFibreChart B hπ E) ⁻¹'
      Set.range (middleFibreChart B hπ E) = Set.range (Reciprocal.toInfinityChart k) := by
  change outerExceptionalBranch hπ ⁻¹' (leftFibreChart B hπ E ⁻¹' Set.range (middleFibreChart B hπ
    E)) = _
  rw [leftFibre_preimage_middle]
  change (outerExceptionalBranch hπ ≫
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))) residueBase) ⁻¹'
      (uniformizerVOpen π : Set (Spec (.of (PlaneNode.Ring π)))) = _
  rw [outerExceptionalBranch_fst]
  ext x
  change _ ↔ x ∈ (Reciprocal.toInfinityChart k).opensRange
  rw [Reciprocal.infinityChart_range]
  change (residueRightHom π (residue_uniformizer hπ)) (PlaneNode.V π) ∉ x.asIdeal ↔
    Polynomial.X ∉ x.asIdeal
  rw [residueRightHom, PlaneNode.lift_V]

lemma rightExceptional_preimage_middle :
    (outerExceptionalBranch hπ ≫ rightFibreChart B hπ E) ⁻¹'
      Set.range (middleFibreChart B hπ E) = Set.range (Reciprocal.toInfinityChart k) := by
  change outerExceptionalBranch hπ ⁻¹' (rightFibreChart B hπ E ⁻¹' Set.range (middleFibreChart B
    hπ E)) = _
  rw [rightFibre_preimage_middle]
  change (outerExceptionalBranch hπ ≫
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))) residueBase) ⁻¹'
      (uniformizerVOpen π : Set (Spec (.of (PlaneNode.Ring π)))) = _
  rw [outerExceptionalBranch_fst]
  ext x
  change _ ↔ x ∈ (Reciprocal.toInfinityChart k).opensRange
  rw [Reciprocal.infinityChart_range]
  change (residueRightHom π (residue_uniformizer hπ)) (PlaneNode.V π) ∉ x.asIdeal ↔
    Polynomial.X ∉ x.asIdeal
  rw [residueRightHom, PlaneNode.lift_V]

lemma oldLeftEnd_preimage_left (hm : algebraMap R k (π ^ m) = 0)
    (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom (residueLeftHom (π ^ m) hm).toRingHom)) :
    (e ≫ middleFibreChart B hπ E) ⁻¹' Set.range (leftFibreChart B hπ E) =
      Set.range (Reciprocal.toZeroChart k) := by
  change e ⁻¹' (middleFibreChart B hπ E ⁻¹' Set.range (leftFibreChart B hπ E)) = _
  rw [middleFibre_preimage_left]
  change (e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map) ⁻¹'
    (uOpen π m : Set (Resolution.X π m)) = _
  rw [he]
  ext x
  change _ ↔ x ∈ (Reciprocal.toZeroChart k).opensRange
  rw [Reciprocal.zeroChart_range]
  change (residueLeftHom (π ^ m) hm) (PlaneNode.U (π ^ m)) ∉ x.asIdeal ↔ Polynomial.X ∉ x.asIdeal
  rw [residueLeftHom, PlaneNode.lift_U]

lemma oldRightEnd_preimage_right (hm : algebraMap R k (π ^ m) = 0)
    (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom (residueRightHom (π ^ m) hm).toRingHom)) :
    (e ≫ middleFibreChart B hπ E) ⁻¹' Set.range (rightFibreChart B hπ E) =
      Set.range (Reciprocal.toZeroChart k) := by
  change e ⁻¹' (middleFibreChart B hπ E ⁻¹' Set.range (rightFibreChart B hπ E)) = _
  rw [middleFibre_preimage_right]
  change (e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map) ⁻¹'
    (vOpen π m : Set (Resolution.X π m)) = _
  rw [he]
  ext x
  change _ ↔ x ∈ (Reciprocal.toZeroChart k).opensRange
  rw [Reciprocal.zeroChart_range]
  change (residueRightHom (π ^ m) hm) (PlaneNode.V (π ^ m)) ∉ x.asIdeal ↔ Polynomial.X ∉ x.asIdeal
  rw [residueRightHom, PlaneNode.lift_V]

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeComponentChartRanges





section NodeFibreComponentEmbeddings

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
variable {π : R} (hπ : Irreducible π) (m : ℕ)
  (B : OneStepBlowup.Data π (m + 1)) (E : Data π (m + 1))
local notation "k" => IsLocalRing.ResidueField R

/-- The old-end affine chart is an exact target-open pullback of the constructed P1. -/
lemma stepLeftCompactification_zero_isPullback (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueLeftHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) :
    IsPullback e (chart k 0) (middleFibreChart B hπ E)
      (stepLeftCompactification hπ m B E e he hb) :=
  Reciprocal.descend_zero_isPullback k (middleFibreChart B hπ E) (leftFibreChart B hπ E)
    e (outerExceptionalBranch hπ) (left_end_reciprocal hπ m B E e he hb)
    (leftExceptional_preimage_middle hπ B E)

/-- The new exceptional affine chart is the other exact target-open pullback. -/
lemma stepLeftCompactification_infinity_isPullback (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueLeftHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) :
    IsPullback (outerExceptionalBranch hπ) (chart k 1) (leftFibreChart B hπ E)
      (stepLeftCompactification hπ m B E e he hb) :=
  Reciprocal.descend_infinity_isPullback k (middleFibreChart B hπ E) (leftFibreChart B hπ E)
    e (outerExceptionalBranch hπ) (left_end_reciprocal hπ m B E e he hb)
    (oldLeftEnd_preimage_left hπ B E (residue_uniformizer_pow hπ m) e he)

lemma stepLeftCompactification_closedImmersion (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueLeftHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k)
      [IsClosedImmersion e] :
    IsClosedImmersion (stepLeftCompactification hπ m B E e he hb) := by
  let U : Fin 2 → Scheme := fun | 0 => sourceSpecialFibre E | 1 => outerFibre (π := π)
  let j : ∀ i, U i ⟶ sourceSpecialFibre (step B hπ E) :=
    fun | 0 => middleFibreChart B hπ E | 1 => leftFibreChart B hπ E
  let c : ∀ i, Reciprocal.affineLine k ⟶ U i :=
    fun | 0 => e | 1 => outerExceptionalBranch hπ
  have hj : ∀ i, IsOpenImmersion (j i) := by intro i; fin_cases i <;> dsimp [j] <;> infer_instance
  have hc : ∀ i, IsClosedImmersion (c i) := by intro i; fin_cases i <;> dsimp [c] <;> infer_instance
  let := hj
  let := hc
  apply Reciprocal.closedImmersion_of_pullbackCharts k _
    (pullback.snd ((step B hπ E).map ≫ base) residueBase)
    (stepLeftCompactification_base hπ m B E e he hb) U j c
  intro i
  fin_cases i
  · exact stepLeftCompactification_zero_isPullback hπ m B E e he hb
  · exact stepLeftCompactification_infinity_isPullback hπ m B E e he hb

/-- The new strict-transform A1 and its neighboring P1 meet scheme-theoretically
in the literal residue-field point at the infinity endpoint. -/
lemma stepLeftEnd_compactification_isPullback (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueLeftHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) :
    IsPullback (Cross.endpoint k) (Reciprocal.infinitySection k)
      (stepLeftEnd hπ B E) (stepLeftCompactification hπ m B E e he hb) := by
  have h := ((outer_branches_isPullback hπ).flip.paste_horiz
    (stepLeftCompactification_infinity_isPullback hπ m B E e he hb).flip).flip
  exact h

/-- The old-end affine chart is an exact target-open pullback of the constructed P1. -/
lemma stepRightCompactification_zero_isPullback (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueRightHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) :
    IsPullback e (chart k 0) (middleFibreChart B hπ E)
      (stepRightCompactification hπ m B E e he hb) :=
  Reciprocal.descend_zero_isPullback k (middleFibreChart B hπ E) (rightFibreChart B hπ E)
    e (outerExceptionalBranch hπ) (right_end_reciprocal hπ m B E e he hb)
    (rightExceptional_preimage_middle hπ B E)

/-- The new exceptional affine chart is the other exact target-open pullback. -/
lemma stepRightCompactification_infinity_isPullback (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueRightHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) :
    IsPullback (outerExceptionalBranch hπ) (chart k 1) (rightFibreChart B hπ E)
      (stepRightCompactification hπ m B E e he hb) :=
  Reciprocal.descend_infinity_isPullback k (middleFibreChart B hπ E) (rightFibreChart B hπ E)
    e (outerExceptionalBranch hπ) (right_end_reciprocal hπ m B E e he hb)
    (oldRightEnd_preimage_right hπ B E (residue_uniformizer_pow hπ m) e he)

lemma stepRightCompactification_closedImmersion (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueRightHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k)
      [IsClosedImmersion e] :
    IsClosedImmersion (stepRightCompactification hπ m B E e he hb) := by
  let U : Fin 2 → Scheme := fun | 0 => sourceSpecialFibre E | 1 => outerFibre (π := π)
  let j : ∀ i, U i ⟶ sourceSpecialFibre (step B hπ E) :=
    fun | 0 => middleFibreChart B hπ E | 1 => rightFibreChart B hπ E
  let c : ∀ i, Reciprocal.affineLine k ⟶ U i :=
    fun | 0 => e | 1 => outerExceptionalBranch hπ
  have hj : ∀ i, IsOpenImmersion (j i) := by intro i; fin_cases i <;> dsimp [j] <;> infer_instance
  have hc : ∀ i, IsClosedImmersion (c i) := by intro i; fin_cases i <;> dsimp [c] <;> infer_instance
  let := hj
  let := hc
  apply Reciprocal.closedImmersion_of_pullbackCharts k _
    (pullback.snd ((step B hπ E).map ≫ base) residueBase)
    (stepRightCompactification_base hπ m B E e he hb) U j c
  intro i
  fin_cases i
  · exact stepRightCompactification_zero_isPullback hπ m B E e he hb
  · exact stepRightCompactification_infinity_isPullback hπ m B E e he hb

/-- The new strict-transform A1 and its neighboring P1 meet scheme-theoretically
in the literal residue-field point at the infinity endpoint. -/
lemma stepRightEnd_compactification_isPullback (e : Cross.line k ⟶ sourceSpecialFibre E)
    (he : e ≫ pullback.fst (E.map ≫ base) residueBase ≫ E.map =
      Spec.map (CommRingCat.ofHom
        (residueRightHom (π ^ (m + 1)) (residue_uniformizer_pow hπ m)).toRingHom))
    (hb : e ≫ pullback.snd (E.map ≫ base) residueBase = Reciprocal.affineBase k) :
    IsPullback (Cross.endpoint k) (Reciprocal.infinitySection k)
      (stepRightEnd hπ B E) (stepRightCompactification hπ m B E e he hb) := by
  have h := ((outer_branches_isPullback hπ).flip.paste_horiz
    (stepRightCompactification_infinity_isPullback hπ m B E e he hb).flip).flip
  exact h

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeFibreComponentEmbeddings
